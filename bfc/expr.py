# This is a part of Esotope Brainfuck compiler.

"""Provides the expression class and canonicalization routines.

The expression in the Brainfuck IL is defined as a set of pure (no I/O),
non-destructive (no memory write) operations. In C terminology the expression
represents r-value. It still references the outside memory and variables.
"""

_EXPRNEG = '_'
_EXPRREF = '@'
_EXPRADD = '+'
_EXPRMUL = '*'
_EXPRDIV = '/'
_EXPRMOD = '%'
_EXPRARITYMAP = {_EXPRNEG: 1, _EXPRREF: 1, _EXPRADD: 2, _EXPRMUL: 2,
                 _EXPRDIV: 2, _EXPRMOD: 2}

class _ExprMeta(type):
    def __getitem__(self, offset):
        return Expr(Expr(offset).code + [_EXPRREF])

class Expr(object):
    __metaclass__ = _ExprMeta
    __slots__ = ['code']

    NEG = _EXPRNEG
    REF = _EXPRREF
    ADD = _EXPRADD
    MUL = _EXPRMUL
    DIV = _EXPRDIV
    MOD = _EXPRMOD

    def __init__(self, obj=0):
        if isinstance(obj, (int, long)):
            self.code = [obj]
        else:
            if isinstance(obj, Expr): obj = obj.code
            self.code = obj[:]

    def __nonzero__(self):
        return (self != 0)

    def __neg__(self):
        code = self.code
        if len(code) == 1: return Expr(-code[0])
        if code[-1] is _EXPRNEG: return Expr(code[:-1])
        return Expr(code + [_EXPRNEG])

    def __pos__(self):
        return self

    def __add__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] + rhscode[0])
            elif lhscode[0] == 0: return rhs
        elif len(rhscode) == 1:
            if rhscode[0] == 0: return lhs
        return Expr(lhscode + rhscode + [_EXPRADD])

    def __radd__(rhs, lhs):
        return Expr(lhs) + rhs

    def __sub__(lhs, rhs):
        return lhs + (-rhs)

    def __rsub__(rhs, lhs):
        return lhs + (-rhs)

    def __mul__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] * rhscode[0])
            elif lhscode[0] == 0: return Expr()
            elif lhscode[0] == 1: return rhs
            elif lhscode[0] == -1: return -rhs
        elif len(rhscode) == 1:
            if rhscode[0] == 0: return Expr()
            elif rhscode[0] == 1: return lhs
            elif rhscode[0] == -1: return -lhs
        return Expr(lhscode + rhscode + [_EXPRMUL])

    def __rmul__(rhs, lhs):
        return Expr(lhs) * rhs

    def __div__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] / rhscode[0])
            elif lhscode[0] == 0: return Expr()
        elif len(rhscode) == 1:
            if rhscode[0] == 1: return lhs
            elif rhscode[0] == -1: return -lhs
        return Expr(lhscode + rhscode + [_EXPRDIV])

    def __rdiv__(rhs, lhs):
        return Expr(lhs) / rhs

    __truediv__ = __div__
    __rtruediv__ = __rdiv__
    __floordiv__ = __div__
    __rfloordiv__ = __rdiv__

    def __mod__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1 and len(rhscode) == 1:
            return Expr(lhscode[0] % rhscode[0])
        return Expr(lhscode + rhscode + [_EXPRMOD])

    def __rmod__(rhs, lhs):
        return Expr(lhs) % rhs

    def __eq__(self, rhs):
        return self.code == Expr(rhs).code

    def __ne__(self, rhs):
        return self.code != Expr(rhs).code

    def __lt__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue < rhsvalue
        except: return False

    def __le__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue <= rhsvalue
        except: return False

    def __gt__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue > rhsvalue
        except: return False

    def __ge__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue >= rhsvalue
        except: return False

    def __hash__(self):
        if self.simple():
            return hash(self.code[0])
        return hash(tuple(self.code))

    def __int__(self):
        assert self.simple()
        return self.code[0]

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

    def _getpartial(self, code, i):
        arityneeded = []
        while True:
            arityneeded.append(_EXPRARITYMAP.get(code[i], 0))
            while arityneeded[-1] == 0:
                del arityneeded[-1]
                if not arityneeded: return i
                arityneeded[-1] -= 1
            i -= 1

    def simple(self):
        return len(self.code) == 1

    def simplify(self):
        return Expr(self._simplify(self.code))

    def references(self):
        code = self.code
        if len(code) == 1:
            return set()
        elif len(code) == 2 and code[1] is _EXPRREF:
            return set([code[0]])

        getpartial = self._getpartial

        refs = set()
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                refs.add(Expr(code[getpartial(code, i-1):i]))
        return refs

    def movepointer(self, delta):
        code = self.code
        if len(code) == 1:
            return Expr(code)
        elif len(code) == 2 and code[1] is _EXPRREF:
            return Expr([code[0] + delta, _EXPRREF])

        getpartial = self._getpartial
        simplify = self._simplify

        newcode = []
        lastref = 0
        i = 0
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                assert isinstance(code[i-1], (int, long)) # XXX
                newcode.extend(code[lastref:i-1])
                newcode.append(code[i-1] + delta)
                lastref = i # this contains _EXPRREF, which is copied later
        newcode.extend(code[lastref:])
        return Expr(newcode)

    def withmemory(self, map):
        code = self.code
        if len(code) == 1:
            return Expr(code)
        elif len(code) == 2 and code[1] is _EXPRREF:
            try: return map[code[0]]
            except KeyError: return Expr(code)

        getpartial = self._getpartial

        newcode = []
        lastref = 0
        i = 0
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                assert isinstance(code[i-1], (int, long)) # XXX
                newcode.extend(code[lastref:i-1])
                try:
                    newcode.extend(Expr(map[code[i-1]]).code)
                except KeyError:
                    newcode.extend(code[i-1:i+1])
                lastref = i + 1
        newcode.extend(code[lastref:])
        return Expr(self._simplify(newcode))

    def __repr__(self):
        stack = []
        for c in self.code:
            if c is _EXPRNEG:
                arg = stack.pop()
                stack.append('-%s' % arg)
            elif c is _EXPRREF:
                arg = stack.pop()
                stack.append('{%s}' % arg)
            elif c is _EXPRADD:
                rhs = stack.pop(); lhs = stack.pop()
                if rhs.startswith('-'):
                    stack.append('(%s%s)' % (lhs, rhs))
                else:
                    stack.append('(%s+%s)' % (lhs, rhs))
            elif c is _EXPRMUL:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s*%s)' % (lhs, rhs))
            elif c is _EXPRDIV:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s/%s)' % (lhs, rhs))
            elif c is _EXPRMOD:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s%%%s)' % (lhs, rhs))
            else:
                stack.append(str(c))
        return stack[-1]

