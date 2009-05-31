# This is a part of Esotope Brainfuck Compiler.

from collections import defaultdict

def isnumber(obj):
    return isinstance(obj, (int, long))

class _termsset(dict):
    """Hashable multiset holds terms in the commutative operations. It mostly
    works like dict, but it cannot be modified normally and has + operator.

    ("Normally" means it can be modified using dict methods directly, but it
    will make __hash__ undeterministic.)
    """

    def __init__(self, iterable=None):
        dict.__init__(self)
        if isinstance(iterable, dict):
            dict.update(self, iterable)
        elif iterable is not None:
            for k, v in iterable:
                v += dict.get(self, k, 0)
                if v == 0:
                    dict.pop(self, k, None)
                else:
                    dict.__setitem__(self, k, v)

    # these methods cannot be used.
    def __setitem__(self, key, value): raise RuntimeError, 'dict is immutable'
    def __delitem__(self, key): raise RuntimeError, 'dict is immutable'
    def clear(self): raise RuntimeError, 'dict is immutable'
    def setdefault(self,k,default=None): raise RuntimeError, 'dict is immutable'
    def popitem(self): raise RuntimeError, 'dict is immutable'
    def update(self, other): raise RuntimeError, 'dict is immutable'

    # XXX i'm not sure that even __init__ can change the order of items
    # undeterministically. (we can use sorted(), but it took so much time
    # and moreover it couldn't be used in python 3.)
    def __hash__(self): return hash(tuple(self.iteritems()))

    def __add__(lhs, rhs):
        result = dict(lhs) # convert to mutable
        for k, v in rhs.items():
            v += result.get(k, 0)
            if v == 0:
                result.pop(k, None)
            else:
                result[k] = v
        return _termsset(result)


_EXPRREF = '@' # (_EXPRREF, offset)
_EXPRVAR = '$' # (_EXPRVAR, name)
_EXPRADD = '+' # (_EXPRADD, const, {term: coefficient, ...})
_EXPRMUL = '*' # (_EXPRMUL, {term: multiplicity, ...})
_EXPRDIV = '//' # (_EXPRDIV, lhs, rhs)
_EXPREXACTDIV = '/' # (_EXPREXACTDIV, lhs, rhs)
_EXPRMOD = '%' # (_EXPRMOD, lhs, rhs)

class _ExprMeta(type):
    """Metaclass of Expr. Used to implement Expr[] syntax."""

    def __getitem__(self, offset):
        """Expr[offset] -> Expr object

        Makes the expression represents memory reference. offset is relative
        to (implicit) current pointer."""

        return Expr((_EXPRREF, Expr(offset).code))

class Expr(object):
    """Expression class with canonicalization.

    Expression is extensively used in the Brainfuck IL, as it is a lot readable
    in the output than a set of operations, and easier to implement certain
    operations. Expression is immutable, but could be internally canonicalized.

    Internally expression is stored as the postfix notation, where number
    represents the leaf node for number, string is for the operation (like
    _EXPRNEG, _EXPRREF, _EXPRADD etc.), and tuple is for extensions (not used
    yet). Arity of operators is implicit and defined in _EXPRARITYMAP."""

    __metaclass__ = _ExprMeta
    __slots__ = ['code']

    REF = _EXPRREF
    VAR = _EXPRVAR
    ADD = _EXPRADD
    MUL = _EXPRMUL
    DIV = _EXPRDIV
    EXACTDIV = _EXPREXACTDIV
    MOD = _EXPRMOD

    def __init__(self, obj=0):
        """Expr(number=0) -> number
        Expr(code) -> Expr
        Expr(exprobj) -> copy of exprobj

        Creates the new expression object: normally it is used to create
        an expression for a number (provide the number to the argument).
        If the argument is not a number, it copies given internal notation
        or object and creates the clone."""

        if isinstance(obj, Expr): obj = obj.code
        self.code = obj

    def __nonzero__(self):
        """expr.__nonzero__() -> bool

        Expression is non-zero if and only if the internal representation is
        not equal to 0. Non-canonical expression like "{0}-{0}" is also non-zero.
        """

        # self.code can be tuple (complex expr) or int/long (simple).
        # since tuple in the expr cannot be empty, the latter is only case
        # bool(self.code) could return False.
        return bool(self.code)

    def __neg__(self):
        code = self.code
        if isnumber(code): return Expr(-code)

        if code[0] is _EXPRADD: # -(_EXPRADD, ...)
            _, const, terms = code
            negatedterms = _termsset([(k, -v) for k, v in terms.items()])
            return Expr((_EXPRADD, -const, negatedterms))

        # treat it as (0 - self).
        return Expr((_EXPRADD, 0, _termsset([(code, -1)])))

    def __pos__(self):
        return self

    def __add__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code

        if isnumber(lhscode):
            if isnumber(rhscode): # number + number
                return Expr(lhscode + rhscode)
            elif lhscode == 0: # 0 + ...
                return rhs
            elif rhscode[0] is _EXPRADD: # number + (_EXPRADD, ...)
                _, const, terms = rhscode
                const += lhscode
            else: # number + ...
                const = lhscode
                terms = _termsset([(rhscode, 1)])

        elif lhscode[0] is _EXPRADD:
            if isnumber(rhscode): # (_EXPRADD, ...) + number
                _, const, terms = lhscode
                const += rhscode
            elif rhscode[0] is _EXPRADD: # (_EXPRADD, ...) + (_EXPRADD, ...)
                _, lconst, lterms = lhscode
                _, rconst, rterms = rhscode
                const = lconst + rconst
                terms = lterms + rterms
            else: # (_EXPRADD, ...) + ...
                _, const, terms = lhscode
                terms += _termsset([(rhscode, 1)])

        elif rhscode == 0: # ... + 0
            return lhs
        elif isnumber(rhscode): # ... + number
            const = rhscode
            terms = _termsset([(lhscode, 1)])
        elif rhscode[0] is _EXPRADD: # ... + (_EXPRADD, ...)
            _, const, terms = rhscode
            terms += _termsset([(lhscode, 1)])

        else:
            const = 0
            terms = _termsset([(lhscode, 1), (rhscode, 1)])

        if terms:
            return Expr((_EXPRADD, const, terms))
        else:
            return const

    def __radd__(rhs, lhs):
        return Expr(lhs) + rhs

    def __sub__(lhs, rhs):
        return lhs + (-rhs)

    def __rsub__(rhs, lhs):
        return lhs + (-rhs)

    def __mul__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code

        if isnumber(lhscode):
            if isnumber(rhscode): # number * number
                return Expr(lhscode * rhscode)
            elif lhscode == 0: # 0 * ...
                return Expr(0)
            elif lhscode == 1: # 1 * ...
                return rhs
            elif lhscode == -1: # -1 * ... (redirect to __neg__)
                return -rhs
            elif rhscode[0] is _EXPRADD: # number * (_EXPRADD, ...)
                _, const, terms = rhscode
                const = lhscode * const
                terms = _termsset((k, lhscode * v) for k, v in terms.items())
                return Expr((_EXPRADD, const, terms))
            else: # number * ...
                return Expr((_EXPRADD, 0, _termsset([(rhscode, lhscode)])))

        elif isnumber(rhscode):
            if rhscode == 0: # ... * 0
                return Expr(0)
            elif rhscode == 1: # ... * 1
                return lhs
            elif rhscode == -1: # ... * -1
                return -lhs
            elif lhscode[0] is _EXPRADD: # (_EXPRADD, ...) * number
                _, const, terms = lhscode
                const = rhscode * const
                terms = _termsset((k, rhscode * v) for k, v in terms.items())
                return Expr((_EXPRADD, const, terms))
            else: # ... * number
                return Expr((_EXPRADD, 0, _termsset([(lhscode, rhscode)])))

        elif lhscode[0] is _EXPRMUL:
            if rhscode[0] is _EXPRMUL: # (_EXPRMUL, ...) * (_EXPRMUL, ...)
                return Expr((_EXPRMUL, lhscode[1] + rhscode[1]))
            else: # (_EXPRMUL, ...) * ...
                return Expr((_EXPRMUL, lhscode[1] + _termsset([(rhscode, 1)])))
        elif rhscode[0] is _EXPRMUL: # ... * (_EXPRMUL, ...)
            return Expr((_EXPRMUL, rhscode[1] + _termsset([(lhscode, 1)])))

        return Expr((_EXPRMUL, _termsset([(lhscode, 1), (rhscode, 1)])))

    def __rmul__(rhs, lhs):
        return Expr(lhs) * rhs

    def __truediv__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code

        if isnumber(lhscode):
            if isnumber(rhscode): # number / number
                assert lhscode % rhscode == 0, \
                        'exact division failed: %r / %r' % (lhscode, rhscode)
                return Expr(lhscode // rhscode)

        elif rhscode == 1: # ... / 1
            return lhs
        elif rhscode == -1: # ... / -1
            return -lhs

        return Expr((_EXPREXACTDIV, lhscode, rhscode))

    def __rtruediv__(rhs, lhs):
        return Expr(lhs) / rhs

    __div__ = __truediv__
    __rdiv__ = __rtruediv__

    def __floordiv__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code

        if isnumber(lhscode):
            if isnumber(rhscode): # number // number
                return Expr(lhscode // rhscode)

        elif rhscode == 1: # ... // 1
            return lhs
        elif rhscode == -1: # ... // -1
            return -lhs

        return Expr((_EXPRDIV, lhscode, rhscode))

    def __rfloordiv__(rhs, lhs):
        return Expr(lhs) // rhs

    def __mod__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code

        if isnumber(lhscode) and isnumber(rhscode): # number % number
            return Expr(lhscode % rhscode)

        return Expr((_EXPRMOD, lhscode, rhscode))

    def __rmod__(rhs, lhs):
        return Expr(lhs) % rhs

    def __eq__(self, rhs):
        return self.code == Expr(rhs).code

    def __ne__(self, rhs):
        return self.code != Expr(rhs).code

    def __lt__(lhs, rhs):
        rhs = Expr(rhs)
        if isnumber(lhs.code) and isnumber(rhs.code):
            return lhs.code < rhs.code
        else:
            return False

    def __le__(lhs, rhs):
        rhs = Expr(rhs)
        if isnumber(lhs.code) and isnumber(rhs.code):
            return lhs.code <= rhs.code
        else:
            return False

    def __gt__(lhs, rhs):
        rhs = Expr(rhs)
        if isnumber(lhs.code) and isnumber(rhs.code):
            return lhs.code > rhs.code
        else:
            return False

    def __ge__(lhs, rhs):
        rhs = Expr(rhs)
        if isnumber(lhs.code) and isnumber(rhs.code):
            return lhs.code >= rhs.code
        else:
            return False

    def __hash__(self):
        return hash(self.code)

    def __int__(self):
        assert self.simple()
        return self.code

    '''
    def _simplify(self, code):
        stack = []

        for c in code:
            if c is _EXPRNEG:
                arg = stack.pop()
                if len(arg) == 1: result = [-arg[0]]
                elif arg[-1] is _EXPRNEG: result = arg[:-1]
                else: result = arg + [_EXPRNEG]

            elif c is _EXPRREF:
                arg = stack.pop()
                result = arg + [_EXPRREF]

            elif c is _EXPRADD:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRADD]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] + rhs[0]]
                    elif lhs[0] == 0: result = rhs
                elif len(rhs) == 1:
                    if rhs[0] == 0: result = lhs

            elif c is _EXPRMUL:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRMUL]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] * rhs[0]]
                    elif lhs[0] == 0: result = [0]
                    elif lhs[0] == 1: result = rhs
                    elif lhs[0] == -1: result = rhs + [_EXPRNEG]
                elif len(rhs) == 1:
                    if rhs[0] == 0: result = [0]
                    elif rhs[0] == 1: result = lhs
                    elif rhs[0] == -1: result = lhs + [_EXPRNEG]

            elif c is _EXPRDIV:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRDIV]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] / rhs[0]]
                    elif lhs[0] == 0: result = []
                elif len(rhs) == 1:
                    if rhs[0] == 1: result = lhs
                    elif rhs[0] == -1: result = lhs + [_EXPRNEG]

            elif c is _EXPRMOD:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRMOD]
                if len(lhs) == 1 and len(rhs) == 1:
                    result = [lhs[0] % rhs[0]]

            else:
                result = [c]

            stack.append(result)

        return stack[-1]
    '''

    def simple(self):
        return isnumber(self.code)

    def simplify(self):
        # XXX
        return self#return Expr(self._simplify(self.code))

    def _references(self, code, result):
        if isnumber(code):
            pass

        elif code[0] is _EXPRREF:
            self._references(code[1], result)
            result.add(Expr(code[1]))

        elif code[0] is _EXPRADD:
            for term in code[2].keys():
                self._references(term, result)
            
        elif code[0] is _EXPRMUL:
            for term in code[1].keys():
                self._references(term, result)

        elif code[0] is _EXPRDIV or code[0] is _EXPREXACTDIV or code[0] is _EXPRMOD:
            self._references(code[1], result)
            self._references(code[2], result)

        else:
            assert False

    def references(self):
        """Returns the set of memory cells (possibly other Expr) the current
        expression references."""

        result = set()
        self._references(self.code, result)
        return result

    def _movepointer(self, code, delta):
        if isnumber(code):
            return code

        elif code[0] is _EXPRREF:
            offset = self._movepointer(code[1], delta)
            return (_EXPRREF, (Expr(offset) + delta).code)

        elif code[0] is _EXPRADD:
            terms = []
            for k, v in code[2].items():
                terms.append((self._movepointer(k, delta), v))
            return (_EXPRADD, code[1], _termsset(terms))

        elif code[0] is _EXPRMUL:
            terms = []
            for k, v in code[1].items():
                terms.append((self._movepointer(k, delta), v))
            return (_EXPRMUL, _termsset(terms))

        elif code[0] is _EXPRDIV or code[0] is _EXPREXACTDIV or code[0] is _EXPRMOD:
            lhs = self._movepointer(code[1], delta)
            rhs = self._movepointer(code[2], delta)
            return (code[0], lhs, rhs)

        else:
            assert False

    def movepointer(self, delta):
        return Expr(self._movepointer(self.code, delta))

    def _withmemory(self, code, map):
        if isnumber(code):
            return code

        elif code[0] is _EXPRREF:
            offset = self._withmemory(code[1], map)
            if isnumber(offset):
                try: return map[offset].code
                except: pass
            return (_EXPRREF, offset)

        elif code[0] is _EXPRADD:
            terms = []
            const = code[1]
            for k, v in code[2].items():
                k = self._withmemory(k, map)
                if isnumber(k):
                    const += k * v
                else:
                    terms.append((k, v))

            if terms:
                return (_EXPRADD, const, _termsset(terms))
            else:
                return const # reduced to simple expression

        elif code[0] is _EXPRMUL:
            terms = []
            const = 1
            for k, v in code[1].items():
                k = self._withmemory(k, map)
                if isnumber(k):
                    const *= k ** v
                else:
                    terms.append((k, v))

            if terms:
                if const == 0:
                    return 0
                elif const == 1:
                    return (_EXPRMUL, _termsset(terms))
                else:
                    return (_EXPRADD, 0, _termsset([((_EXPRMUL, _termsset(terms)), const)]))
            else:
                return const # reduced to simple expression

        elif code[0] is _EXPRDIV:
            lhs = self._withmemory(code[1], map)
            rhs = self._withmemory(code[2], map)

            if isnumber(lhs) and isnumber(rhs):
                return lhs // rhs
            else:
                return (_EXPRDIV, lhs, rhs)

        elif code[0] is _EXPREXACTDIV:
            lhs = self._withmemory(code[1], map)
            rhs = self._withmemory(code[2], map)

            if isnumber(lhs) and isnumber(rhs):
                assert lhs % rhs == 0, 'exact division failed: %r / %r' % (lhs, rhs)
                return lhs // rhs
            else:
                return (_EXPREXACTDIV, lhs, rhs)

        elif code[0] is _EXPRMOD:
            lhs = self._withmemory(code[1], map)
            rhs = self._withmemory(code[2], map)

            if isnumber(lhs) and isnumber(rhs):
                return lhs % rhs
            else:
                return (_EXPRMOD, lhs, rhs)

        else:
            assert False

    def withmemory(self, map):
        return Expr(self._withmemory(self.code, map))

    def _compactrepr(self, code):
        try:
            op = code[0]
        except:
            return str(code)

        _compactrepr = self._compactrepr

        if op is _EXPRREF:
            _, offset = code
            return '{%s}' % _compactrepr(offset)

        if op is _EXPRVAR:
            _, name = code
            return '$%s' % name

        if op is _EXPRADD:
            _, const, terms = code
            result = []
            for k, v in terms.items():
                if v == -1: result.append('-%s' % _compactrepr(k))
                elif v == 1: result.append('+%s' % _compactrepr(k))
                else: result.append('%+d*%s' % (v, _compactrepr(k)))
            terms = ''.join(result).lstrip('+')
            if const != 0:
                return '(%s%+d)' % (terms, const)
            else:
                return '(%s)' % terms

        if op is _EXPRMUL:
            _, terms = code
            terms = '*'.join(map(_compactrepr, terms))
            return '(%s)' % terms

        if op is _EXPRDIV or op is _EXPREXACTDIV or op is _EXPRMOD:
            op, lhs, rhs = code
            return '(%s%s%s)' % (_compactrepr(lhs), op, _compactrepr(rhs))

        assert False

    def compactrepr(self):
        return self._compactrepr(self.code)

    def __repr__(self):
        return '<Expr: %s>' % self.compactrepr()

