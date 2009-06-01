# This is a part of Esotope Brainfuck compiler.

"""The Brainfuck IL (intermediate language).

Brainfuck IL is an internal representation of source code in Esotope compiler.
It depends on the expression (bfc.expr module) and condition (bfc.cond module)
objects.
"""

from bfc.expr import *
from bfc.cond import *

def _setmovepointer(cells, offset):
    """Adds given offset to every elements in cells, except for None (normally
    represents "one or more other cells")."""

    result = [i + offset for i in cells if i is not None]
    if None in cells: result.append(None)
    return set(result)

class cellset(object):
    __slots__ = ('sure', 'unsure')

    def __init__(self, sure=None, unsure=None, others=None):
        self.sure = set(sure or ())
        self.unsure = set(unsure or ()) | self.sure
        if others: self.sure.add(None)
        if others is not None: self.unsure.add(None)

    def copy(self):
        return cellset(sure=self.sure, unsure=self.unsure)

    def addsure(self, item):
        self.sure.add(item)
        self.unsure.add(item)

    def addunsure(self, item):
        self.unsure.add(item)

    def updatesure(self, items):
        self.sure.update(items)
        self.unsure.update(items)

    def updateunsure(self, items):
        self.unsure.update(items)

    def clearsure(self):
        self.sure.clear()

    def clearunsure(self):
        self.unsure = self.sure.copy()

    def itersure(self):
        return iter(self.sure - set([None]))

    def iterunsure(self):
        return iter(self.unsure - set([None]))

    def movepointer(self, offsets):
        if offsets == 0: return self.copy()
        return cellset(sure=_setmovepointer(self.sure, offsets),
                       unsure=_setmovepointer(self.unsure, offsets))

    def __nonzero__(self):
        return bool(self.sure) and bool(self.unsure)

    def __eq__(lhs, rhs):
        return lhs.sure == rhs.sure and lhs.unsure == rhs.unsure

    def __ne__(lhs, rhs):
        return lhs.sure != rhs.sure or lhs.unsure != rhs.unsure

    def __ior__(lhs, rhs):
        lhs.sure |= rhs.sure
        lhs.unsure |= rhs.unsure
        return lhs
    update = __ior__

    def __or__(lhs, rhs):
        return cellset(sure=lhs.sure | rhs.sure, unsure=lhs.unsure | rhs.unsure)

    def __iand__(lhs, rhs):
        lhs.sure &= rhs.sure
        lhs.unsure &= rhs.unsure
        return lhs

    def __and__(lhs, rhs):
        return cellset(sure=lhs.sure & rhs.sure, unsure=lhs.unsure & rhs.unsure)

    def __isub__(lhs, rhs):
        lhs.sure -= rhs.sure
        lhs.unsure -= rhs.unsure
        return lhs

    def __sub__(lhs, rhs):
        return cellset(sure=lhs.sure - rhs.sure, unsure=lhs.unsure - rhs.unsure)

    def _repr_set(self, set):
        set = set.copy()
        try:
            set.remove(None)
            if not set: return '[...]'
            return '[%s, ...]' % repr(list(set))[1:-1]
        except KeyError:
            return repr(list(set))

    def __repr__(self):
        return 'cellset(%s, %s)' % (self._repr_set(self.sure),
                                    self._repr_set(self.unsure - self.sure))


class Node(object):
    """Base class of the Brainfuck IL."""

    def __nonzero__(self):
        """node.__nonzero__() -> bool

        Should return False if it is a unconditionally no-op."""

        return True

    def pure(self):
        """node.pure() -> bool

        Should return False if it does any input or output, thus cannot be
        reordered. This includes any loop contains I/O node."""

        return True

    def movepointer(self, offset):
        """node.movepointer(offset) -> None

        Moves all memory references in the node by given offset. This is an
        in-place operation."""

        raise RuntimeError('not implemented')

    # propagates known memory cells given.
    def withmemory(self, map):
        pass

    # a set of offset to memory cells which may be referenced/updated by
    # this node, relative to initial pointer before execution.
    # these methods are used for forward analysis.
    def prereferences(self): return cellset()
    def preupdates(self): return cellset()

    # amount of pointer moves. it differs with amount of pointer moves
    # in the loop body only -- use ComplexNode.stride() for it.
    # it may return None if uncertain.
    def offsets(self): return 0

    # similar to pre* methods, but the offsets are relative to final pointer
    # after execution. these methods are used for backward analysis.
    # note that these will be same to pre* ones if offsets() returns 0.
    def postreferences(self): return cellset()
    def postupdates(self): return cellset()

    # returns False if this node is an infinite loop.
    def returns(self): return True

    def compactrepr(self):
        raise RuntimeError('not implemented')

    def __repr__(self):
        return self.compactrepr()

class ComplexNode(Node, list):
    def empty(self):
        return len(self) > 0

    def movepointer(self, offset):
        if offset != 0:
            for child in self: child.movepointer(offset)

    def pure(self):
        return all(child.pure() for child in self)

    def stride(self):
        stride = 0
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None: return None
            stride += ioffsets
        return stride

    def bodyprereferences(self):
        offsets = 0
        refs = cellset()
        for child in self:
            refs |= child.prereferences().movepointer(offsets)
            ioffsets = child.offsets()
            if ioffsets is None:
                refs.addsure(None)
                break
            offsets += ioffsets
        return refs

    def bodypreupdates(self):
        offsets = 0
        updates = cellset()
        for child in self:
            updates |= child.preupdates().movepointer(offsets)
            ioffsets = child.offsets()
            if ioffsets is None:
                updates.addsure(None)
                break
            offsets += ioffsets
        return updates

    def bodypostreferences(self):
        offsets = 0
        refs = cellset()
        for child in self[::-1]:
            ioffsets = child.offsets()
            if ioffsets is None:
                refs.addsure(None)
                break
            offsets -= ioffsets
            refs |= child.postreferences().movepointer(offsets)
        return refs

    def bodypostupdates(self):
        offsets = 0
        updates = cellset()
        for child in self[::-1]:
            ioffsets = child.offsets()
            if ioffsets is None:
                updates.addsure(None)
                break
            offsets -= ioffsets
            updates |= child.postupdates().movepointer(offsets)
        return updates

    def _innerrepr(self):
        return ', '.join(child.compactrepr() for child in self)

class Program(ComplexNode):
    """Program node.
    
    Program[...] represents the entire program, including any necessary setups
    for Brainfuck program.
    """

    def compactrepr(self):
        return 'Program[%s]' % self._innerrepr()

class Nop(Node):
    """Nop node.

    Nop[] is a designated no-op node, used as a placeholder and later removed
    by cleanup pass.
    """

    def __nonzero__(self):
        return False

    def compactrepr(self):
        return 'Nop[]'

class UseVariable(ComplexNode):
    def __init__(self, vars, children=[]):
        ComplexNode.__init__(self, children)
        self.vars = vars

    def __nonzero__(self):
        return len(self) > 0

    offsets = ComplexNode.stride
    prereferences = ComplexNode.bodyprereferences
    postreferences = ComplexNode.bodypostreferences
    preupdates = ComplexNode.bodypreupdates
    postupdates = ComplexNode.bodypostupdates

    def compactrepr(self):
        return 'UseVariable[%s; %s]' % (', '.join('$%s' % i for i in self.vars),
                                        self._innerrepr())

class SetMemory(Node):
    """SetMemory node.

    SetMemory[offset, value], or {offset}=value in the compact notation,
    represents that the memory cell at the offset (relative to the current
    pointer) is set to given value (possibly an expression).

    SetMemory is one of two memory operations in the Brainfuck IL. The other
    one is AdjustMemory.
    """

    def __init__(self, offset, value):
        self.offset = offset
        self.value = Expr(value)

    def movepointer(self, offset):
        self.offset += offset
        self.value = self.value.movepointer(offset)

    def withmemory(self, map):
        self.value = self.value.withmemory(map)

    def prereferences(self):
        return cellset(sure=self.value.references())
    postreferences = prereferences

    def preupdates(self):
        return cellset(sure=[self.offset])
    postupdates = preupdates

    def compactrepr(self):
        return '{%d}=%s' % (self.offset, self.value.compactrepr())

    def __repr__(self):
        return 'SetMemory[%d, %s]' % (self.offset, self.value.compactrepr())

class AdjustMemory(Node):
    """AdjustMemory node.

    AdjustMemory[offset, value], or {offset}+=value and {offset}-=value in the
    compact notation, is equivalent to {offset}={offset}+value and {offset}=
    {offset}-value respectively.

    AdjustMemory is added for convenience, as current canonicalization routine
    cannot handle complex expression like ({x}+v)-{x}. We plan to improve the
    canonicalization routine thus remove the need for AdjustMemory entirely.
    """

    def __init__(self, offset, delta):
        self.offset = offset
        self.delta = Expr(delta)

    def __nonzero__(self):
        return self.delta != 0

    def movepointer(self, offset):
        self.offset += offset
        self.delta = self.delta.movepointer(offset)

    def withmemory(self, map):
        self.delta = self.delta.withmemory(map)

    def prereferences(self):
        return cellset(sure=self.delta.references().union([self.offset]))
    postreferences = prereferences

    def preupdates(self):
        return cellset(sure=[self.offset])
    postupdates = preupdates

    def compactrepr(self):
        if self.delta < 0:
            return '{%d}-=%s' % (self.offset, (-self.delta).compactrepr())
        else:
            return '{%d}+=%s' % (self.offset, self.delta.compactrepr())

    def __repr__(self):
        return 'AdjustMemory[%d, %s]' % (self.offset, self.delta.compactrepr())

class MovePointer(Node):
    """MovePointer node.

    MovePointer[offset] represents the pointer movement by given offset. It is
    relatively rare, as the parser already propagated almost all < and >
    commands except at the end of the loop.
    """

    def __init__(self, offset):
        self.offset = offset

    def __nonzero__(self):
        return self.offset != 0

    def movepointer(self, offset):
        pass # no change

    def offsets(self):
        return self.offset

    def compactrepr(self):
        return 'MovePointer[%d]' % self.offset

class Input(Node):
    """Input node.

    {offset}=Input[] reads one byte from the input and stores it to given
    memory cell. Despite the notation, it cannot be merged to the expression
    since I/O should not be reordered. (For example, if Input[] appears in
    the expression how to interpret "{x}=Input[]+Input[]*2"?)
    """

    def __init__(self, offset):
        self.offset = offset

    def pure(self):
        return False

    def movepointer(self, offset):
        self.offset += offset

    def preupdates(self):
        return cellset(sure=[self.offset])
    postupdates = preupdates

    def compactrepr(self):
        return '{%d}=Input[]' % self.offset

class Output(Node):
    """Output node.

    Output[expr] writes one byte, typically calculated by expr modulo 256, to
    the output. Like Input[] it cannot be reordered.

    There is OutputConst[...] node for printing many constant characters.
    """

    def __init__(self, expr):
        self.expr = Expr(expr)

    def pure(self):
        return False

    def withmemory(self, map):
        self.expr = self.expr.withmemory(map)

    def prereferences(self):
        return cellset(sure=self.expr.references())
    postreferences = prereferences

    def movepointer(self, offset):
        self.expr = self.expr.movepointer(offset)

    def compactrepr(self):
        return 'Output[%s]' % self.expr.compactrepr()

class OutputConst(Node):
    """OutputConst node.

    OutputConst["string"] writes "string" to the output. It is equivalent to
    Output[ord(string[0])], Output[ord(string[1])], ... and produced by stdlib
    pass at the very end of optimization.
    """

    def __init__(self, s):
        if isinstance(s, str):
            self.str = s
        else:
            self.str = ''.join(chr(i & 0xff) for i in s)

    def __nonzero__(self):
        return len(self.str) > 0

    def pure(self):
        return False

    def movepointer(self, offset):
        pass # does nothing

    def compactrepr(self):
        return 'OutputConst[%r]' % self.str

class SeekMemory(Node):
    """SeekMemory node.

    SeekMemory[{p+q*k}!=x] seeks the memory cell {p}, {p+q}, {p+2*q}, ... and
    determintes the first one which value is not equal to x. It then moves the
    current pointer by q*k, so that {p} is guaranteed to be not equal to x.

    It is equal to While[{p}!=x; MovePointer[q]], but it is very common array
    operation so treated specially.
    """

    def __init__(self, target, stride, value=0):
        self.target = target
        self.stride = stride
        self.value = value

    def offsets(self):
        return None

    def movepointer(self, offset):
        self.target += offset

    def prereferences(self):
        return cellset(sure=[self.target], others=False)

    def postreferences(self):
        return cellset(sure=[self.target], others=False)

    def compactrepr(self):
        if self.target == 0:
            return 'SeekMemory[{%d*k}!=%d]' % (self.stride, self.value)
        elif self.stride < 0:
            return 'SeekMemory[{%d-%d*k}!=%d]' % (self.target, -self.stride, self.value)
        else:
            return 'SeekMemory[{%d+%d*k}!=%d]' % (self.target, self.stride, self.value)

class If(ComplexNode):
    """If node.

    If[cond; ...] is the conditional node which executes its body if the given
    condition holds. Some If[] nodes are equivalent to While[] node, but If[]
    allows arbitrary condition.
    """

    def __init__(self, cond=None, children=[]):
        ComplexNode.__init__(self, children)
        if cond is None:
            self.cond = MemNotEqual(0, 0)
        else:
            self.cond = cond

    def __nonzero__(self):
        return bool(self.cond) and len(self) > 0

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.cond = self.cond.movepointer(offset)

    def withmemory(self, map):
        self.cond = self.cond.withmemory(map)

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        return cellset(sure=self.cond.references(),
                       unsure=self.bodyprereferences().unsure)

    def postreferences(self):
        bodyrefs = cellset(unsure=self.bodypostreferences().unsure)
        stride = self.stride()
        if stride is not None:
            bodyrefs.updatesure(_setmovepointer(self.cond.references(), -stride))
        else:
            bodyrefs.addsure(None) # we don't know where it is.
        return bodyrefs

    def preupdates(self):
        return cellset(unsure=self.bodypreupdates().unsure)

    def postupdates(self):
        return cellset(unsure=self.bodypostupdates().unsure)

    def compactrepr(self):
        return 'If[%s; %s]' % (self.cond.compactrepr(), self._innerrepr())

class Repeat(ComplexNode):
    """Repeat node.

    Repeat[count; ...] executes its body count times. Count can be an
    expression, but only evaluated once before the loop.
    """

    def __init__(self, count, children=[]):
        ComplexNode.__init__(self, children)
        self.count = Expr(count)

    def __nonzero__(self):
        return bool(self.count) and len(self) > 0

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.count = self.count.movepointer(offset)

    def withmemory(self, map):
        self.count = self.count.withmemory(map)

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        bodyrefs = cellset(sure=self.count.references(),
                           unsure=self.bodyprereferences().unsure)
        stride = self.stride()
        if stride != 0:
            bodyrefs.addunsure(None)
        return bodyrefs

    def postreferences(self):
        bodyrefs = cellset(unsure=self.bodypostreferences().unsure)
        stride = self.stride()
        if stride is not None:
            bodyrefs.updatesure(_setmovepointer(self.count.references(), -stride))
        if stride != 0:
            bodyrefs.addunsure(None)
        return bodyrefs

    def preupdates(self):
        bodyupdates = cellset(unsure=self.bodypreupdates().unsure)
        stride = self.stride()
        if stride != 0:
            bodyupdates.addunsure(None)
        return bodyupdates

    def postupdates(self):
        bodyupdates = cellset(unsure=self.bodypostupdates().unsure)
        stride = self.stride()
        if stride != 0:
            bodyupdates.addunsure(None)
        return bodyupdates

    def compactrepr(self):
        return 'Repeat[%s; %s]' % (self.count.compactrepr(), self._innerrepr())

class While(ComplexNode):
    """While node.

    While[cond; ...] executes its body repeatedly until the condition holds.
    This is a basic, and only form of control flow in Brainfuck; every other
    construct is converted from this node.
    """

    def __init__(self, cond, children=[]):
        ComplexNode.__init__(self, children)
        self.cond = cond

    def __nonzero__(self):
        # infinite loop should return True, even if there are no children.
        return bool(self.cond)

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.cond = self.cond.movepointer(offset)

    def withmemory(self, map):
        # updates condition only if the loop will be never executed.
        newcond = self.cond.withmemory(map)
        if isinstance(newcond, Never): self.cond = newcond

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        bodyrefs = cellset(sure=self.cond.references(),
                           unsure=self.bodyprereferences().unsure)
        stride = self.stride()
        if stride != 0:
            bodyrefs.addunsure(None)
        return bodyrefs

    def postreferences(self):
        bodyrefs = cellset(sure=self.cond.references(),
                           unsure=self.bodypostreferences().unsure)
        stride = self.stride()
        if stride != 0:
            bodyrefs.addunsure(None)
        return bodyrefs

    def preupdates(self):
        bodyupdates = cellset(unsure=self.bodypreupdates().unsure)
        stride = self.stride()
        if stride != 0:
            bodyupdates.addunsure(None)
        return bodyupdates

    def postupdates(self):
        bodyupdates = cellset(unsure=self.bodypostupdates().unsure)
        stride = self.stride()
        if stride != 0:
            bodyupdates.addunsure(None)
        return bodyupdates

    def returns(self):
        return not isinstance(self.cond, Always)

    def compactrepr(self):
        return 'While[%s; %s]' % (self.cond.compactrepr(), self._innerrepr())

