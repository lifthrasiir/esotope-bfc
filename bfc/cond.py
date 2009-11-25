# This is a part of Esotope Brainfuck compiler.

"""The condition objects.

Condition object is an extension to expression: it provides comparison
operator. It is used in While and If nodes in the Brainfuck IL.
"""

import operator as _operator
from bfc.utils import *
from bfc.expr import *

class Condition(genobject):
    """Base class of condition expression in Brainfuck IL. Likewise expression,
    condition is immutable and always canonicalized."""

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

    def __and__(lhs, rhs): return Conjunction(lhs, rhs)
    def __rand__(rhs, lhs): return Conjunction(lhs, rhs)
    def __or__(lhs, rhs): return Disjunction(lhs, rhs)
    def __ror__(rhs, lhs): return Disjunction(lhs, rhs)

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

    def compactrepr(self, prec=0):
        """Returns a compact string notation of this condition. See also
        Expr.compactrepr."""

        raise NotImplementedError # pragma: no cover

    def __repr__(self):
        return '<Cond: %s>' % self.compactrepr()


class Always(Condition):
    """Tautology (notation: True). Always evaluates to true value."""

    def __invert__(self):
        return Never()

    @property
    def args(self):
        return ()

    def references(self): return frozenset()
    def movepointer(self, offset): return self
    def withmemory(self, map): return self
    def compactrepr(self, prec=0): return 'True'

class Never(Condition):
    """Contradiction (notation: False). Always evaluates to false value."""

    def __nonzero__(self):
        return False

    def __invert__(self):
        return Always()

    @property
    def args(self):
        return ()

    def references(self): return frozenset()
    def movepointer(self, offset): return self
    def withmemory(self, map): return self
    def compactrepr(self, prec=0): return 'False'


def _intersect_range(lhs, rhs):
    nextlhs = iter(lhs).next
    nextrhs = iter(rhs).next
    try:
        lmin, lmax = nextlhs()
        rmin, rmax = nextrhs()
    except StopIteration:
        return []

    result = []
    while True:
        min = lmin; max = lmax
        if rmin is not None and (min is None or min < rmin): min = rmin
        if rmax is not None and (max is None or max > rmax): max = rmax
        if min is None or max is None or min <= max:
            # [lmin,lmax] and [rmin,rmax] actually overlap each other
            result.append((min, max))
        if max == lmax: # lmax <= rmax
            try: lmin, lmax = nextlhs()
            except StopIteration: break
        if max == rmax: # lmax >= rmax
            try: rmin, rmax = nextrhs()
            except StopIteration: break
    return result

class Range(Condition):
    """The condition that the expression is in one of the given intervals
    (notation: expr in (1..2, 3..4, 5..6); expr in (..2, 3..4, 5..);
    for only one interval: min<=expr<=max, min<=expr and expr<=max).

    Intervals are disjoint and inclusive to both ends, and the first and
    last intervals are possibly unlimited to one end. In that case,
    the plus infinity and minus infinity are represented as None.
    """

    __slots__ = ('expr', 'ranges')

    def __gen__(cls, expr, *ranges):
        # normalize ranges as list of (min,max) tuples
        ranges = list(ranges)
        offset = 0
        for i in xrange(len(ranges)):
            try: min, max = ranges[i]
            except: min = max = ranges[i]
            if min is not None: min = int(min)
            if max is not None: max = int(max)
            if min is not None and max is not None and min > max:
                offset += 1
            else:
                ranges[i-offset] = min, max
        else:
            if offset: del ranges[-offset:]

        expr = Expr(expr)
        if expr.simple(): # reduces to constant
            v = int(expr)
            for min, max in ranges:
                if (min is None or min <= v) and (max is None or v <= max):
                    return Always()
            else:
                return Never()

        while True:
            if isinstance(expr, LinearExpr):
                if expr[0] != 0: # min <= const + ... <= max
                    const = expr[0]
                    expr = LinearExpr(*expr[1:])
                    for i in xrange(len(ranges)):
                        min, max = ranges[i]
                        if min is not None: min -= const
                        if max is not None: max -= const
                        ranges[i] = min, max
                    continue

                if len(expr) == 2: # min <= 0 + coeff * term <= max
                    coeff = abs(expr[1][0])
                    changesign = (expr[1][0] < 0)
                    expr = expr[1][1]
                    offset = 0
                    for i in xrange(len(ranges)):
                        min, max = ranges[i]
                        if changesign:
                            min, max = max, min
                            if min is not None: min = (-min - 1) // coeff + 1
                            if max is not None: max = -max // coeff
                        else:
                            if min is not None: min = (min - 1) // coeff + 1
                            if max is not None: max = max // coeff
                        if min is not None and max is not None and min > max:
                            offset += 1
                        else:
                            ranges[i-offset] = min, max
                    else:
                        if offset: del ranges[-offset:]
                    continue

            if isinstance(expr, ExactDivisionExpr): # min <= term / div <= max
                if expr.rhs.simple():
                    rhs = int(expr.rhs)
                    expr = expr.lhs
                    for i in xrange(len(ranges)):
                        min, max = ranges[i]
                        if min is not None: min *= rhs
                        if max is not None: max *= rhs
                        ranges[i] = min, max
                    continue

            break # no more reduction possible

        if not ranges: return Never()
        ranges.sort(key=lambda (min,max): (min is not None, min, max is None, max))

        result = []
        lastmin, lastmax = ranges[0]
        for min, max in ranges[1:]:
            # if [lastmin,lastmax] and [min,max] is consecutive or overlaps
            # each other, merge them into [lastmin,max{max,lastmax}].
            if lastmax is None or min is None or lastmax + 1 >= min:
                if max is None or (lastmax is not None and lastmax < max):
                    lastmax = max
            else:
                result.append((lastmin, lastmax))
                lastmin = min; lastmax = max
        result.append((lastmin, lastmax))

        if len(result) == 0:
            return Never()
        elif len(result) == 1 and result[0][0] == result[0][1]:
            if result[0][0] is None:
                return Always()
            else:
                return Equal(expr, result[0][0])
        elif (len(result) == 2 and result[0][0] is None and
                                   result[0][1] == result[1][0] - 2 and
                                   result[1][1] is None):
            return NotEqual(expr, result[0][1]+1)
        else:
            return Condition.__gen__(cls, expr, *result)

    def __init__(self, expr, *ranges):
        self.expr = expr
        self.ranges = ranges

    def __invert__(self):
        ranges = self.ranges
        newranges = []
        if ranges[0][0] is not None:
            newranges.append((None, ranges[0][0]-1))
        for i in xrange(len(ranges)-1):
            newranges.append((ranges[i][1]+1, ranges[i+1][0]-1))
        if ranges[-1][1] is not None:
            newranges.append((ranges[-1][1]+1, None))
        return Range(self.expr, *newranges)

    @property
    def args(self):
        return (self.expr,) + self.ranges

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        return Range(self.expr.movepointer(offset), *self.ranges)

    def withmemory(self, map):
        return Range(self.expr.withmemory(map), *self.ranges)

    def compactrepr(self, prec=0):
        expr = self.expr.compactrepr()
        if len(self.ranges) == 1:
            min, max = self.ranges[0]
            if min is None:
                return '%s<=%r' % (expr, max)
            elif max is None:
                return '%r<=%s' % (min, expr)
            else:
                return '%r<=%s<=%r' % (min, expr, max)
        else:
            clauses = []
            for min, max in self.ranges:
                if min is None: clauses.append('..%r' % max)
                elif max is None: clauses.append('%r..' % min)
                elif min == max: clauses.append(repr(min))
                else: clauses.append('%r..%r' % (min, max))
            return '%s~(%s)' % (expr, ','.join(clauses))

# shortcuts
def Between(min, expr, max): return Range(expr, (min, max))
def Less(expr, value): return Range(expr, (None, value-1))
def LessOrEqual(expr, value): return Range(expr, (None, value))
def Greater(expr, value): return Range(expr, (value+1, None))
def GreaterOrEqual(expr, value): return Range(expr, (value, None))


class _EqualityCond(Condition):
    """The conditions that the expression is equal or not equal to the integer
    value. Corresponding subclasses are Equal and NotEqual, respectively.

    _MemEqualityCond is a special case that the expression is a reference to
    fixed (i.e. simple integer) memory cell.
    """

    __slots__ = ('expr', 'value')

    def __gen__(cls, expr, value=0):
        expr = Expr(expr)
        if expr.simple():
            if cls.negated ^ (int(expr) == value):
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
        self.value = int(value)

    @property
    def args(self):
        return (self.expr, self.value)

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        return self.base_class(self.expr.movepointer(offset), self.value)

    def withmemory(self, map):
        return self.base_class(self.expr.withmemory(map), self.value)

class Equal(_EqualityCond):
    """The condition that the expression is equal to the integer value
    (notation: expr==v). See also _EqualityCond.
    """

    negated = False

    def __invert__(self):
        return NotEqual(self.expr, self.value)

    def compactrepr(self, prec=0):
        if self.value == 0:
            return '!' + self.expr.compactrepr(9) # "sufficiently large" prec!
        else:
            return '%s==%r' % (self.expr.compactrepr(), self.value)

class NotEqual(_EqualityCond):
    """The condition that the expression is not equal to the integer value
    (notation: expr!=v). See also _EqualityCond.
    """

    negated = True

    def __invert__(self):
        return Equal(self.expr, self.value)

    def compactrepr(self, prec=0):
        if self.value == 0:
            return self.expr.compactrepr()
        else:
            return '%s!=%r' % (self.expr.compactrepr(), self.value)

Equal.base_class = Equal
NotEqual.base_class = NotEqual


class _MemEqualityCond(_EqualityCond):
    """The conditions that the value of given memory cell is equal or not equal
    to the integer value. Corresponding subclasses are MemEqual and MemNotEqual,
    respectively.

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

class MemNotEqual(_MemEqualityCond, NotEqual):
    """The condition that the value of given memory cell is not equal to
    the integer value (notation: {p}!=v). See also _MemEqualityCond.
    """

NotEqual.memref_class = MemNotEqual
Equal.memref_class = MemEqual


class Conjunction(Condition, tuple):
    """The conditions that are a conjunction of other conditions, i.e. AND'ed
    clauses (notation: cond&&cond&&...).
    """

    def __gen__(cls, *clauses):
        # merge Range conditions by depdending cells
        ranges = {}
        result = []
        for clause in clauses:
            if not isinstance(clause, Conjunction):
                clause = [clause]
            for iclause in clause:
                if isinstance(iclause, Always):
                    continue
                elif isinstance(iclause, Never):
                    return Never()
                else:
                    if isinstance(iclause, Range):
                        newrr = iclause.ranges
                    elif isinstance(iclause, Equal):
                        newrr = [(iclause.value, iclause.value)]
                    elif isinstance(iclause, NotEqual):
                        newrr = [(None, iclause.value-1), (iclause.value+1, None)]
                    else:
                        result.append(iclause)
                        continue

                    try: rr = ranges[iclause.expr]
                    except KeyError: rr = [(None, None)]
                    ranges[iclause.expr] = _intersect_range(rr, newrr)

        for expr, rr in ranges.items():
            result.append(Range(expr, *rr))
        result.sort(key=hash)

        if not result:
            return Always()
        elif len(result) == 1:
            return result[0]
        else:
            return tuple.__new__(cls, result)

    @property
    def args(self):
        return tuple(self)

    def __invert__(self):
        return Disjunction(*map(_operator.invert, self))

    def references(self):
        return reduce(_operator.or_, [c.references() for c in self], frozenset())

    def movepointer(self, offset):
        return Conjunction(*[c.movepointer(offset) for c in self])

    def withmemory(self, map):
        return Conjunction(*[c.withmemory(map) for c in self])

    def compactrepr(self, prec=0):
        result = ' && '.join(c.compactrepr(2) for c in self)
        if prec > 1 and len(self) > 1: result = '(%s)' % result
        return result

class Disjunction(Condition, tuple):
    """The conditions that are a disjunction of other conditions, i.e. OR'ed
    clauses (notation: cond||cond||...).
    """

    def __gen__(cls, *clauses):
        # merge Range conditions by depdending cells
        ranges = {}
        result = []
        for clause in clauses:
            if not isinstance(clause, Disjunction):
                clause = [clause]
            for iclause in clause:
                if isinstance(iclause, Always):
                    return Always()
                elif isinstance(iclause, Never):
                    continue
                else:
                    if isinstance(iclause, Range):
                        newrr = iclause.ranges
                    elif isinstance(iclause, Equal):
                        newrr = [(iclause.value, iclause.value)]
                    elif isinstance(iclause, NotEqual):
                        newrr = [(None, iclause.value-1), (iclause.value+1, None)]
                    else:
                        result.append(iclause)
                        continue

                    ranges.setdefault(iclause.expr, []).extend(newrr)

        for expr, rr in ranges.items():
            result.append(Range(expr, *rr))
        result.sort(key=hash)

        if not result:
            return Never()
        elif len(result) == 1:
            return result[0]
        else:
            return tuple.__new__(cls, result)

    @property
    def args(self):
        return tuple(self)

    def __invert__(self):
        return Conjunction(*map(_operator.invert, self))

    def references(self):
        return reduce(_operator.or_, [c.references() for c in self], frozenset())

    def movepointer(self, offset):
        return Disjunction(*[c.movepointer(offset) for c in self])

    def withmemory(self, map):
        return Disjunction(*[c.withmemory(map) for c in self])

    def compactrepr(self, prec=0):
        result = ' || '.join(c.compactrepr(2) for c in self)
        if prec > 1 and len(self) > 1: result = '(%s)' % result
        return result

