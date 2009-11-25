# This is a part of Esotope Brainfuck Compiler.

import operator as _operator
from bfc.utils import *

class _ExprMeta(gentype):
    """Metaclass of Expr. Used to implement Expr[] syntax."""

    def __getitem__(self, offset):
        """Expr[offset] -> Expr object

        Makes the expression represents memory reference. offset is relative
        to (implicit) current pointer."""

        return ReferenceExpr(offset)

class Expr(genobject):
    """Expression class with canonicalization.

    Expression is extensively used in the Brainfuck IL, as it is a lot readable
    in the output than a set of operations, and easier to implement certain
    operations. Expression is immutable, and always canonicalized."""

    __metaclass__ = _ExprMeta

    def __gen__(cls, obj=0):
        if isinstance(obj, Expr): return obj
        return LinearExpr(int(obj))

    def __nonzero__(self):
        """expr.__nonzero__() -> bool

        Expression is non-zero if and only if the internal representation is
        not equal to 0. Non-canonical expression like "{0}-{0}" is also non-zero.
        """

        return True

    def __pos__(self): return self
    def __neg__(self): return LinearExpr((-1, self))

    def __add__(lhs, rhs): return LinearExpr(lhs, rhs)
    def __radd__(rhs, lhs): return LinearExpr(lhs, rhs)
    def __sub__(lhs, rhs): return LinearExpr(lhs, (-1, rhs))
    def __rsub__(rhs, lhs): return LinearExpr(lhs, (-1, rhs))
    def __mul__(lhs, rhs): return MultiplyExpr(lhs, rhs)
    def __rmul__(rhs, lhs): return MultiplyExpr(lhs, rhs)
    def __truediv__(lhs, rhs): return ExactDivisionExpr(lhs, rhs)
    def __rtruediv__(rhs, lhs): return ExactDivisionExpr(lhs, rhs)
    __div__ = __truediv__
    __rdiv__ = __rtruediv__
    def __floordiv__(lhs, rhs): return DivisionExpr(lhs, rhs)
    def __rfloordiv__(rhs, lhs): return DivisionExpr(lhs, rhs)
    def __mod__(lhs, rhs): return ModuloExpr(lhs, rhs)
    def __rmod__(rhs, lhs): return ModuloExpr(lhs, rhs)

    def simple(self):
        """Returns True if the expression reduces to single integer."""

        return False

    def references(self):
        """Returns the set of memory cells (possibly other Expr or variable
        symbols) the current expression references."""

        raise NotImplementedError # pragma: no cover

    def movepointer(self, offset):
        """Returns new expression with all memory reference is shifted by given
        offset. For example, {3} shifted by 4 is {7} and {{5}+6} shifted by -1
        is {{4}+5}."""

        raise NotImplementedError # pragma: no cover

    def withmemory(self, map):
        """Returns new expression with all memory reference present in the
        given map replaced by its value. The map is mapping from memory
        offset to its current value. The result is automatically
        canonicalized."""

        raise NotImplementedError # pragma: no cover

    def compactrepr(self, prec=0):
        """Returns a compact string notation of this expression. The additional
        argument, if any, is a precedence of outer node, and used for correct
        parenthesizing. (Hint: with sufficient large prec value almost all
        expression will be parenthesized.)"""

        raise NotImplementedError # pragma: no cover

    def __repr__(self):
        return '<Expr: %s>' % self.compactrepr()

class _ExprNode(Expr):
    """Base class for every expression node."""

    __gen__ = genobject.__gen__

    def __hash__(self):
        return hash(tuple.__add__((self.__class__,), self.args))

    def __eq__(lhs, rhs):
        rhs = Expr(rhs)
        return type(lhs) == type(rhs) and lhs.args == rhs.args

    def __ne__(lhs, rhs):
        rhs = Expr(rhs)
        return type(lhs) != type(rhs) or lhs.args != rhs.args

class ReferenceExpr(_ExprNode):
    """Memory reference node (notation: {expr}).

    There is no other information about referenced cell. For example, there
    is no indication of range of the cell's value. If you really want it,
    you have to substitute all memory references {k} with {k}%cellsize.
    """

    __slots__ = ('offset',)

    def __init__(self, offset):
        self.offset = Expr(offset)

    @property
    def args(self):
        return (self.offset,)

    def references(self):
        return frozenset([self.offset]) | self.offset.references()

    def movepointer(self, offset):
        return ReferenceExpr(self.offset.movepointer(offset) + offset)

    def withmemory(self, map):
        newoffset = self.offset.withmemory(map)
        try:
            if newoffset.simple(): return Expr(map[newoffset]).withmemory(map)
        except KeyError:
            pass
        return ReferenceExpr(newoffset)

    def compactrepr(self, prec=0):
        return '{%s}' % self.offset.compactrepr()

class LinearExpr(_ExprNode, tuple):
    """Linear combination node (notation: expr+expr, expr-expr, k*expr,
    -expr, +expr and Expr(number)).

    All linear combination of complex terms is represented as this node.
    For example, ({3}-{4}/2)*5+6 is equivalent to 6+5*{3}-5*({4}/2) and
    internally stored as (6, (5, {3}), (-5, {4}/2)). If there is only one term,
    it should be an integer constant.
    """

    def __gen__(cls, *terms):
        # normalize terms as (const, (coeff1, term1), (coeff2, term2), ...)
        const = 0
        termsmap = {}
        for term in terms:
            try:
                const += int(term)
            except:
                if isinstance(term, Expr):
                    coeff = 1
                else:
                    coeff, term = term
                    coeff = int(coeff)

                if isinstance(term, LinearExpr): # flatten
                    const += coeff * term[0]
                    for icoeff, iterm in term[1:]:
                        termsmap[iterm] = termsmap.get(iterm, 0) + coeff * icoeff
                elif isinstance(term, (int, long)):
                    const += coeff * term
                else:
                    termsmap[term] = termsmap.get(term, 0) + coeff

        args = [const]
        for k, v in termsmap.items():
            if v != 0: args.append((v, k))
        if len(args) == 2 and args[0] == 0 and args[1][0] == 1:
            return args[1][1] # special casing
        return tuple.__new__(cls, args)

    def __nonzero__(self):
        return len(self) != 1 or self[0] != 0

    def __hash__(self):
        if len(self) == 1:
            return hash(self[0])
        else:
            return hash(tuple.__add__((self.__class__,), self))

    @property
    def args(self):
        return tuple(self)

    def simple(self):
        return (len(self) == 1)

    def __int__(self):
        assert len(self) == 1
        return self[0]

    def references(self):
        return reduce(_operator.or_, [k.references() for v, k in self[1:]], frozenset())

    def movepointer(self, offset):
        return LinearExpr(self[0], *[(v, k.movepointer(offset)) for v, k in self[1:]])

    def withmemory(self, map):
        return LinearExpr(self[0], *[(v, k.withmemory(map)) for v, k in self[1:]])

    def compactrepr(self, prec=0):
        result = []
        for v, k in self[1:]:
            if v == -1: result.append('-%s' % k.compactrepr(1))
            elif v == 1: result.append('+%s' % k.compactrepr(1))
            else: result.append('%+d*%s' % (v, k.compactrepr(1)))
        if self[0] != 0:
            result.append('%+d' % self[0])

        if result:
            terms = ''.join(result).lstrip('+')
        else:
            terms = '0'
        if prec > 1 and len(result) > 1:
            terms = '(%s)' % terms
        return terms

class MultiplyExpr(_ExprNode, tuple):
    """Multiplication node (notation: expr*expr).

    This node is used for complex multiplication, e.g. {3}*{4}. If there is
    a constant factor it is represented as LinearExpr.
    """

    def __gen__(cls, *terms):
        # filter integral terms here.
        factor = 1
        realterms = []
        for term in terms:
            try:
                factor *= int(term)
            except:
                if isinstance(term, LinearExpr) and len(term) == 2 and term[0] == 0:
                    factor *= term[1][0]
                    term = term[1][1]
                if isinstance(term, MultiplyExpr):
                    realterms.extend(term)
                else:
                    realterms.append(term)
        realterms.sort(key=hash) # XXX

        if not realterms: # e.g. MultiplyExpr(4, 5)
            return LinearExpr(factor)
        elif factor == 0: # e.g. MultiplyExpr(0, Expr[3])
            return LinearExpr()
        elif factor != 1: # e.g. MultiplyExpr(2, Expr[3])
            return LinearExpr((factor, MultiplyExpr(*realterms)))
        elif len(realterms) == 1: # e.g. MultiplyExpr(Expr[3])
            return realterms[0]
        else:
            return tuple.__new__(cls, realterms)

    @property
    def args(self):
        return tuple(self)

    def references(self):
        return reduce(_operator.or_, [e.references() for e in self], frozenset())

    def movepointer(self, offset):
        return MultiplyExpr(*[e.movepointer(offset) for e in self])

    def withmemory(self, map):
        return MultiplyExpr(*[e.withmemory(map) for e in self])

    def compactrepr(self, prec=0):
        terms = '*'.join(e.compactrepr(2) for e in self)
        if prec > 2 and len(self) > 1: terms = '(%s)' % terms
        return terms

class DivisionExpr(_ExprNode):
    """Floor division node (notation: expr//expr).

    It denotes floor(lhs/rhs). ExactDivisionExpr is used for exact division,
    that is, lhs is known to be a multiple of rhs.
    """
    # XXX consistent semantics for negative dividend and divisor

    __slots__ = ('lhs', 'rhs')

    def __gen__(cls, lhs, rhs):
        try: rvalue = int(rhs)
        except: pass
        else:
            try: lvalue = int(lhs)
            except:
                if rvalue == 1: return lhs
                if rvalue == -1: return -lhs
            else:
                return LinearExpr(lvalue // rvalue)

        return NotImplemented

    def __init__(self, lhs, rhs):
        self.lhs = Expr(lhs)
        self.rhs = Expr(rhs)

    @property
    def args(self):
        return (self.lhs, self.rhs)

    def references(self):
        return self.lhs.references() | self.rhs.references()

    def movepointer(self, offset):
        return DivisionExpr(self.lhs.movepointer(offset), self.rhs.movepointer(offset))

    def withmemory(self, map):
        return DivisionExpr(self.lhs.withmemory(map), self.rhs.withmemory(map))

    def compactrepr(self, prec=0):
        terms = '%s//%s' % (self.lhs.compactrepr(2), self.rhs.compactrepr(3))
        if prec > 3: terms = '(%s)' % terms
        return terms

class ExactDivisionExpr(_ExprNode):
    """Exact division node (notation: expr/expr).

    ExactDivisionExpr differs from DivisionExpr, as this node requires that
    lhs is divisible by rhs. Typically this assumption is asserted externally
    (e.g. with If node in bfc.nodes module) and canonicalization fails if
    this assumption is false.
    """

    __slots__ = ('lhs', 'rhs')

    def __gen__(cls, lhs, rhs):
        try: rvalue = int(rhs)
        except: pass
        else:
            try: lvalue = int(lhs)
            except:
                if rvalue == 1: return lhs
                if rvalue == -1: return -lhs
            else:
                if lvalue % rvalue != 0:
                    raise ValueError('exact division failed: %r / %r' % (lvalue, rvalue))
                return LinearExpr(lvalue // rvalue)

        return NotImplemented

    def __init__(self, lhs, rhs):
        self.lhs = Expr(lhs)
        self.rhs = Expr(rhs)

    @property
    def args(self):
        return (self.lhs, self.rhs)

    def references(self):
        return self.lhs.references() | self.rhs.references()

    def movepointer(self, offset):
        return ExactDivisionExpr(self.lhs.movepointer(offset),
                                 self.rhs.movepointer(offset))

    def withmemory(self, map):
        return ExactDivisionExpr(self.lhs.withmemory(map),
                                 self.rhs.withmemory(map))

    def compactrepr(self, prec=0):
        terms = '%s/%s' % (self.lhs.compactrepr(2), self.rhs.compactrepr(3))
        if prec > 3: terms = '(%s)' % terms
        return terms

class ModuloExpr(_ExprNode):
    """Modulo node (notation: expr%expr).

    From definition of floor division and modulo, (lhs//rhs)*rhs + (lhs%rhs) == lhs.
    In the other words, lhs//rhs == (lhs - lhs%rhs)/rhs. (Note the difference of
    floor division and exact division.)
    """
    # XXX consistent semantics for negative dividend and divisor

    __slots__ = ('lhs', 'rhs')

    def __gen__(cls, lhs, rhs):
        try:
            rvalue = int(rhs)
            lvalue = int(lhs)
        except:
            pass
        else:
            return LinearExpr(int(lhs) % rvalue)

        return NotImplemented

    def __init__(self, lhs, rhs):
        self.lhs = Expr(lhs)
        self.rhs = Expr(rhs)

    @property
    def args(self):
        return (self.lhs, self.rhs)

    def references(self):
        return self.lhs.references() | self.rhs.references()

    def movepointer(self, offset):
        return ModuloExpr(self.lhs.movepointer(offset), self.rhs.movepointer(offset))

    def withmemory(self, map):
        return ModuloExpr(self.lhs.withmemory(map), self.rhs.withmemory(map))

    def compactrepr(self, prec=0):
        terms = '%s%%%s' % (self.lhs.compactrepr(2), self.rhs.compactrepr(3))
        if prec > 3: terms = '(%s)' % terms
        return terms

