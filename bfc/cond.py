# This is a part of Esotope Brainfuck compiler.

"""The condition objects.

Condition object is an extension to expression: it provides comparison
operator. It is used in While and If nodes in the Brainfuck IL.
"""

from bfc.utils import *
from bfc.expr import *

class Condition(genobject):
    """Base class of condition expression in Brainfuck IL."""

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

    def references(self):
        return frozenset()

    def movepointer(self, offset):
        return self

    def withmemory(self, map):
        return self

    def compactrepr(self):
        raise NotImplementedError

    def __repr__(self):
        return '<Cond: %s>' % self.compactrepr()

class Always(Condition):
    @property
    def args(self):
        return ()

    def compactrepr(self):
        return 'True'

class Never(Condition):
    def __nonzero__(self):
        return False

    @property
    def args(self):
        return ()

    def compactrepr(self):
        return 'False'

class NotEqual(Condition):
    __slots__ = ('expr', 'value')

    def __gen__(cls, expr, value=0):
        expr = Expr(expr)
        if expr.simple():
            if int(expr) != value:
                return Always()
            else:
                return Never()
        elif isinstance(expr, ReferenceExpr):
            if expr.offset.simple():
                return MemNotEqual(int(expr.offset), value)
        elif isinstance(expr, LinearExpr):
            if expr[0] != 0:
                return NotEqual(LinearExpr(*expr[1:]), value - expr[0])
            elif len(expr) == 2: # 0 + coeff * term
                if abs(value) % abs(expr[1][0]) == 0:
                    return NotEqual(expr[1][1], value // expr[1][0])
                else:
                    return Always()
        elif isinstance(expr, ExactDivisionExpr):
            if expr.rhs.simple():
                return NotEqual(expr.lhs, value * int(expr.rhs))

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
        return NotEqual(self.expr.movepointer(offset), self.value)

    def withmemory(self, map):
        expr = self.expr.withmemory(map)
        if expr.simple():
            if int(expr) != self.value:
                return Always()
            else:
                return Never()
        else:
            return NotEqual(expr.withmemory(map), self.value)

    def compactrepr(self):
        if self.value == 0:
            return self.expr.compactrepr()
        else:
            return '%s!=%r' % (self.expr.compactrepr(), self.value)

class MemNotEqual(NotEqual):
    def __gen__(self, target, value=0):
        if isinstance(target, Expr) and not target.simple():
            return NotEqual(Expr[target], value)
        return NotImplemented

    def __init__(self, target, value=0):
        NotEqual.__init__(self, Expr[int(target)], value)

    @property
    def target(self):
        return self.expr.offset

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

