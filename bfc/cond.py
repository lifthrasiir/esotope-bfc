# This is a part of Esotope Brainfuck compiler.

"""The condition objects.

Condition object is an extension to expression: it provides comparison
operator. It is used in While and If nodes in the Brainfuck IL.
"""

from bfc.utils import *
from bfc.expr import *

class Condition(genobject):
    """Base class of condition expression in Brainfuck IL.

    One thing special for Condition is negation. Most conditions have negated
    counterparts, but their implementations are so similar that it results in
    very similar code. Thus all conditions implemented here has a common class
    which implements both normal and negated conditions.
    
    By convention, "negated" boolean attribute and "negated_class" class
    reference should be used in the final wrapped classes. In particular,
    two resulting classes should have same constructor signature.
    """

    def __nonzero__(self):
        """cond.__nonzero__() -> bool

        Should return False if it unconditionally evaluates to false."""

        return True

    def __hash__(self):
        return hash(tuple.__add__((self.__class__,), self.args))

    def __eq__(lhs, rhs):
        return type(lhs) == type(rhs) and lhs.args == rhs.args

    def __ne__(lhs, rhs):
        return type(lhs) != type(rhs) or lhs.args != rhs.args

    def __invert__(self):
        return self.negated_class(*self.args)

    @property
    def args(self):
        """(Normalized) arguments passed to the object's constructor."""

        raise NotImplementedError # pragma: no cover

    def references(self):
        """Returns the set of memory cells the current condition references.
        See also Expr.references."""

        raise NotImplementedError # pragma: no cover

    def movepointer(self, offset):
        """Returns new condition with all memory reference is shifted by given
        offset. See also Expr.movepointer."""

        raise NotImplementedError # pragma: no cover

    def withmemory(self, map):
        """Returns new condition with all memory reference present in the
        given map replaced by its value. See also Expr.withmemory."""

        raise NotImplementedError # pragma: no cover

    def compactrepr(self):
        """Returns a compact string notation of this expression. See also
        Expr.compactrepr."""

        raise NotImplementedError # pragma: no cover

    def __repr__(self):
        return '<Cond: %s>' % self.compactrepr()


class _ConstantCond(Condition):
    """Constant conditions. They always evaluate to one logical value
    respectively."""

    def __nonzero__(self):
        return not self.negated

    @property
    def args(self):
        return ()

    def references(self): return frozenset()
    def movepointer(self, offset): return self
    def withmemory(self, map): return self

class Always(_ConstantCond):
    """Tautology (notation: True). See also _ConstantCond."""
    negated = False
    def compactrepr(self): return 'True'

class Never(_ConstantCond):
    """Contradiction (notation: False). See also _ConstantCond."""
    negated = True
    def compactrepr(self): return 'False'

Always.negated_class = Never
Never.negated_class = Always


class _EqualityCond(Condition):
    """The conditions that the expression is equal or not equal to the integer
    value. See also _MemEqualityCond.
    """

    __slots__ = ('expr', 'value')

    def __gen__(cls, expr, value=0):
        expr = Expr(expr)
        if expr.simple():
            if (int(expr) == value) ^ cls.negated:
                return Always()
            else:
                return Never()
        elif isinstance(expr, ReferenceExpr):
            if expr.offset.simple():
                return cls.memref_class(int(expr.offset), value)
        elif isinstance(expr, LinearExpr):
            if expr[0] != 0:
                return cls.base_class(LinearExpr(*expr[1:]), value - expr[0])
            elif len(expr) == 2: # 0 + coeff * term
                if abs(value) % abs(expr[1][0]) == 0:
                    return cls.base_class(expr[1][1], value // expr[1][0])
                elif cls.negated:
                    return Always()
                else:
                    return Never()
        elif isinstance(expr, ExactDivisionExpr):
            if expr.rhs.simple():
                return cls.base_class(expr.lhs, value * int(expr.rhs))

        return NotImplemented

    def __init__(self, expr, value=0):
        self.expr = Expr(expr)
        self.value = value

    @property
    def args(self):
        return (self.expr, self.value)

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        return self.base_class(self.expr.movepointer(offset), self.value)

    def withmemory(self, map):
        expr = self.expr.withmemory(map)
        if expr.simple():
            if (int(expr) == self.value) ^ self.negated:
                return Always()
            else:
                return Never()
        else:
            return self.base_class(expr.withmemory(map), self.value)

class Equal(_EqualityCond):
    """The condition that the expression is equal to the integer value
    (notation: expr==v). See also _EqualityCond.
    """
    negated = False
    def compactrepr(self):
        if self.value == 0:
            return '!' + self.expr.compactrepr(9) # "sufficiently large" prec!
        else:
            return '%s==%r' % (self.expr.compactrepr(), self.value)

class NotEqual(_EqualityCond):
    """The condition that the expression is not equal to the integer value
    (notation: expr!=v). See also _EqualityCond.
    """
    negated = True
    def compactrepr(self):
        if self.value == 0:
            return self.expr.compactrepr()
        else:
            return '%s!=%r' % (self.expr.compactrepr(), self.value)

Equal.negated_class = NotEqual.base_class = NotEqual
NotEqual.negated_class = Equal.base_class = Equal

class _MemEqualityCond(_EqualityCond):
    """The conditions that the value of given memory cell is equal or not equal
    to the integer value.

    They are specializations of normal equality: all Equal or NotEqual objects
    with given condition is converted to MemEqual or MemNotEqual objects, and
    vice versa. Also note that the memory cell referenced is fixed.
    """

    def __gen__(self, target, value=0):
        if isinstance(target, Expr) and not target.simple():
            return self.base_class(Expr[target], value)
        return NotImplemented

    def __init__(self, target, value=0):
        _EqualityCond.__init__(self, Expr[int(target)], value)

    @property
    def target(self):
        return self.expr.offset

    @property
    def args(self):
        return (self.target, self.value)

class MemEqual(_MemEqualityCond, Equal):
    """The condition that the value of given memory cell is equal to
    the integer value (notation: {p}==v). See also _MemEqualityCond.
    """
    base_class = Equal

class MemNotEqual(_MemEqualityCond, NotEqual):
    """The condition that the value of given memory cell is not equal to
    the integer value (notation: {p}!=v). See also _MemEqualityCond.
    """
    base_class = NotEqual

MemEqual.negated_class = NotEqual.memref_class = MemNotEqual
MemNotEqual.negated_class = Equal.memref_class = MemEqual


"""
class NotBetween(Condition):
    __slots__ = ('expr', 'min', 'max')

    def __init__(self, expr, min, max):
        self.expr = Expr(expr)
        self.min = min
        self.max = max

    @property
    def args(self):
        return (self.expr, self.min, self.max)

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        return Between(self.expr.movepointer(offset), self.min, self.max)

    def withmemory(self, map):
        expr = self.expr.withmemory(map)
        if isinstance(expr, LinearExpr):
            # a0 + a1 * x1 + ... + an * xn
            pass
        elif isinstance(expr, MultiplyExpr):
            pass
        else:
            return ExprBetween(expr, self.min, self.max)

    def compactrepr(self):
        return '%r<=%s<=%r' % (self.min, self.expr.compactrepr(), self.max)
"""

