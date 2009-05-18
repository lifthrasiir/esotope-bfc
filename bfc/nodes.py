# This is a part of Esotope Brainfuck-to-C Compiler.

from bfc.expr import *
from bfc.cond import *

def _setmovepointer(cells, offset):
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
    # returns False if it is a no-op. cleanup pass will remove such no-ops.
    def __nonzero__(self): return True

    # returns False if it does an input or output, thus cannot be reordered.
    def pure(self): return True

    # moves all memory references in it by offset.
    def movepointer(self, offset): raise RuntimeError('not implemented')

    # propagates known memory cells given.
    def withmemory(self, map): pass

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

    def __repr__(self):
        return list.__repr__(self)

class Program(ComplexNode):
    def __repr__(self):
        return 'Program[%s]' % ComplexNode.__repr__(self)[1:-1]

class Nop(Node):
    def __nonzero__(self):
        return False

    def __repr__(self):
        return 'Nop[]'

class SetMemory(Node):
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

    def __repr__(self):
        return '{%d}=%r' % (self.offset, self.value)

class AdjustMemory(Node):
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

    def __repr__(self):
        if self.delta < 0:
            return '{%d}-=%r' % (self.offset, -self.delta)
        else:
            return '{%d}+=%r' % (self.offset, self.delta)

class MovePointer(Node):
    def __init__(self, offset):
        self.offset = offset

    def __nonzero__(self):
        return self.offset != 0

    def movepointer(self, offset):
        pass # no change

    def offsets(self):
        return self.offset

    def __repr__(self):
        return 'MovePointer[%r]' % self.offset

class Input(Node):
    def __init__(self, offset):
        self.offset = offset

    def pure(self):
        return False

    def movepointer(self, offset):
        self.offset += offset

    def preupdates(self):
        return cellset(sure=[self.offset])
    postupdates = preupdates

    def __repr__(self):
        return '{%r}=Input[]' % self.offset

class Output(Node):
    def __init__(self, expr):
        self.expr = expr

    def pure(self):
        return False

    def withmemory(self, map):
        self.expr = self.expr.withmemory(map)

    def prereferences(self):
        return cellset(sure=self.expr.references())
    postreferences = prereferences

    def movepointer(self, offset):
        self.expr = self.expr.movepointer(offset)

    def __repr__(self):
        return 'Output[%r]' % self.expr

class OutputConst(Node):
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

    def __repr__(self):
        return 'OutputConst[%r]' % self.str

class SeekMemory(Node):
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

    def __repr__(self):
        if self.target == 0:
            return 'SeekMemory[{%r*k}!=%r]' % (self.stride, self.value)
        else:
            return 'SeekMemory[{%d+%r*k}!=%r]' % \
                    (self.target, self.stride, self.value, self.target)

class If(ComplexNode):
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

    def __repr__(self):
        return 'If[%r; %s]' % (self.cond, ComplexNode.__repr__(self)[1:-1])

class Repeat(ComplexNode):
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

    def __repr__(self):
        return 'Repeat[%r; %s]' % (self.count, ComplexNode.__repr__(self)[1:-1])

class While(ComplexNode):
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

    def __repr__(self):
        return 'While[%r; %s]' % (self.cond, ComplexNode.__repr__(self)[1:-1])

