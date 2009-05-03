#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
from collections import namedtuple
from cStringIO import StringIO

_reprmap = [('\\%03o', '%c')[32 <= i < 127] % i for i in xrange(256)]
_reprmap[0] = '\\0'; _reprmap[9] = '\\t'; _reprmap[10] = '\\n'; _reprmap[13] = '\\r'
_reprmap[34] = '\\"'; _reprmap[39] = '\''; _reprmap[92] = '\\\\'
def _addslashes(s):
    return ''.join(_reprmap[ord(i)] for i in s)


class _ExprMeta(type):
    def __getitem__(self, offset):
        return Expr(Expr.MemoryRef(offset))

class Expr(object):
    __metaclass__ = _ExprMeta
    __slots__ = ['root']

    class _exprbase(tuple):
        def __new__(cls, *args):
            if not args: raise TypeError('empty arguments')
            return tuple.__new__(cls, args)
        def __eq__(self, rhs):
            return self.__class__ is rhs.__class__ and tuple.__eq__(self, rhs)
        def __ne__(self, rhs):
            return self.__class__ is not rhs.__class__ or tuple.__ne__(self, rhs)

    class Number(namedtuple('Number', 'value'), _exprbase):
        def __str__(self): return str(self.value)
        def __repr__(self): return repr(self.value)

        def simplify(self):
            return self

        def apply(self, func, merge=None):
            return func(self)

    class MemoryRef(namedtuple('MemoryRef', 'offset'), _exprbase):
        def __str__(self): return 'mptr[%s]' % self.offset
        def __repr__(self): return 'mptr[%r]' % self.offset

        def simplify(self):
            return self

        def apply(self, func, merge=None):
            return func(self)

    class Negate(namedtuple('Negate', 'expr'), _exprbase):
        def __str__(self): return '-%s' % (self.expr,)
        def __repr__(self): return '-%r' % (self.expr,)

        def simplify(self):
            if isinstance(self.expr, Expr.Number):
                return Expr.Number(-self.expr.value)
            if isinstance(self.expr, Expr.Negate):
                return self.expr
            if isinstance(self.expr, Expr.Sum):
                return Expr.Sum(*[Expr.Negate(child).simplify() for child in self.expr])
            return Expr.Negate(self.expr.simplify())

        def apply(self, func, merge=None):
            return (merge or Expr.Negate)(self.expr.apply(func, merge))

    class Sum(_exprbase):
        def _prettify(self, func):
            items = [func(self[0])]
            for child in self[1:]:
                if isinstance(child, Expr.Negate):
                    items.extend(['-', func(child.expr)])
                elif isinstance(child, Expr.Number) and child.value < 0:
                    items.extend(['-', func(-child.value)])
                else:
                    items.extend(['+', func(child)])
            return items

        def __str__(self): return '(%s)' % ' '.join(self._prettify(str))
        def __repr__(self): return '(%s)' % ''.join(self._prettify(repr))

        def simplify(self):
            result = []
            numbersum = 0
            for child in self:
                child = child.simplify()
                if isinstance(child, Expr.Number):
                    numbersum += child.value
                elif isinstance(child, Expr.Sum):
                    result.extend(child)
                else:
                    result.append(child)
            if numbersum != 0:
                result.append(Expr.Number(numbersum))

            if len(result) == 0:
                return Expr.Number(0)
            elif len(result) == 1:
                return result[0]
            else:
                return Expr.Sum(*result)

        def apply(self, func, merge=None):
            return (merge or Expr.Sum)(*[i.apply(func, merge) for i in self])

    class Product(_exprbase):
        def __str__(self): return '(%s)' % ' * '.join(map(str, self))
        def __repr__(self): return '(%s)' % '*'.join(map(repr, self))

        def simplify(self):
            result = []
            numberprod = 1
            for child in self:
                child = child.simplify()
                if isinstance(child, Expr.Number):
                    numberprod *= child.value
                elif isinstance(child, Expr.Product):
                    result.extend(child)
                else:
                    result.append(child)
            if numberprod != 0:
                result.append(Expr.Number(numberprod))
            else:
                del result[:]

            if len(result) == 0:
                return Expr.Number(0)
            elif len(result) == 1:
                return result[0]
            else:
                return Expr.Product(*result)

        def apply(self, func, merge=None):
            return (merge or Expr.Product)(*[i.apply(func, merge) for i in self])

    def __init__(self, obj=0):
        if isinstance(obj, (int, long)):
            self.root = Expr.Number(obj)
        elif isinstance(obj, Expr):
            self.root = obj.root
        else:
            self.root = obj

    def __neg__(self):
        if isinstance(self.root, Expr.Negate): return Expr(self.root.expr)
        if isinstance(self.root, Expr.Number): return Expr(-self.root.value)
        return Expr(Expr.Negate(self.root))

    def __pos__(self):
        return self

    def __add__(lhs, rhs):
        rhs = Expr(rhs)
        if isinstance(lhs.root, Expr.Number) and isinstance(rhs.root, Expr.Number):
            return Expr(lhs.root.value + rhs.root.value)
        if lhs == 0: return rhs
        if rhs == 0: return lhs

        lhsroot = lhs.root
        rhsroot = rhs.root
        if not isinstance(lhsroot, Expr.Sum): lhsroot = (lhsroot,)
        if not isinstance(rhsroot, Expr.Sum): rhsroot = (rhsroot,)
        return Expr(Expr.Sum(*(lhsroot + rhsroot)))

    def __radd__(rhs, lhs): return Expr(lhs) + rhs
    def __sub__(lhs, rhs): return lhs + (-rhs)
    def __rsub__(rhs, lhs): return lhs + (-rhs)

    def __mul__(lhs, rhs):
        rhs = Expr(rhs)
        if isinstance(lhs.root, Expr.Number) and isinstance(rhs.root, Expr.Number):
            return Expr(lhs.root.value * rhs.root.value)
        if lhs == 0 or rhs == 0: return Expr()
        if lhs == 1: return rhs
        if rhs == 1: return lhs
        if lhs == -1: return -rhs
        if rhs == -1: return -lhs

        lhsroot = lhs.root
        rhsroot = rhs.root
        if not isinstance(lhsroot, Expr.Product): lhsroot = (lhsroot,)
        if not isinstance(rhsroot, Expr.Product): rhsroot = (rhsroot,)
        return Expr(Expr.Product(*(lhsroot + rhsroot)))

    def __rmul__(rhs, lhs): return Expr(lhs) * rhs

    def __eq__(self, rhs):
        return self.root == Expr(rhs).root
    def __ne__(self, rhs):
        return self.root != Expr(rhs).root
    def __lt__(self, rhs):
        try: return self.root.value < Expr(rhs).root.value
        except: return False
    def __le__(self, rhs):
        try: return self.root.value <= Expr(rhs).root.value
        except: return False
    def __gt__(self, rhs):
        try: return self.root.value > Expr(rhs).root.value
        except: return False
    def __ge__(self, rhs):
        try: return self.root.value >= Expr(rhs).root.value
        except: return False

    def __int__(self):
        assert self.simple()
        return self.root.value

    def simple(self):
        return isinstance(self.root, Expr.Number)

    def simplify(self):
        return Expr(self.root.simplify())

    def references(self):
        def func(node):
            if not isinstance(node, Expr.MemoryRef): return set()
            return set([node.offset])
        return self.root.apply(func, set.union)

    def movepointer(self, delta):
        def func(node):
            if not isinstance(node, Expr.MemoryRef): return node
            return Expr.MemoryRef(node.offset + delta)
        return Expr(self.root.apply(func))

    def withmemory(self, map):
        def func(node):
            if not isinstance(node, Expr.MemoryRef): return node
            try: return map[node.offset].root # assume Expr object
            except: return node
        return Expr(self.root.apply(func).simplify())

    def __str__(self):
        return str(self.root)

    def __repr__(self):
        return repr(self.root)


class Node(object):
    # returns False if it is a no-op. minptrmoves pass will remove such no-ops.
    def __nonzero__(self): return True

    # returns False if it does an input or output, thus cannot be reordered.
    def pure(self): return True

    # moves all memory references in it by offset.
    # if it is not possible (like LoopWhile) canmovepointer should return False.
    def canmovepointer(self, offset): return False
    def movepointer(self, offset): raise RuntimeError('not implemented')

    # specifies what this node does. optimizer assumes it does:
    # - changes the pointer by node.offsets().
    # - references (at least) all memory cells in node.references().
    # - updates (at least) all memory cells in node.updates().
    #
    # node.offsets() can return Expr object, or None if uncertain.
    # node.references() and node.updates() is a set containing memory offset
    # relative to the final (after moved by node.offsets()) pointer.
    # if the set contains None, it can reference or update other unspecificed cells.
    def offsets(self): return 0
    def references(self): return set()
    def updates(self): return set()

class ComplexNode(Node, list):
    def __nonzero__(self):
        return len(self) > 0

    def canmovepointer(self, offset):
        if offset == 0: return True
        if self.offsets() != 0: return False
        return all(child.canmovepointer(offset) for child in self)

    def movepointer(self, offset):
        if offset != 0:
            for child in self: child.movepointer(offset)

    def pure(self):
        return all(child.pure() for child in self)

    def offsets(self):
        offsets = 0
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None: return None
            offsets += ioffsets
        return offsets

    def references(self):
        offsets = 0
        refs = []
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None:
                # invalidates prior updates, but not later nor current.
                offsets = 0
                refs = [None]
            refs.extend(i if i is None else i + offsets for i in child.references())

        # should return memory references relative to final pointer.
        return set(i if i is None else i - offsets for i in refs)

    def updates(self):
        offsets = 0
        updates = []
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None:
                offsets = 0
                updates = [None]
            updates.extend(i if i is None else i + offsets for i in child.updates())

        return set(i if i is None else i - offsets for i in updates)

    def __repr__(self):
        return list.__repr__(self)

class Program(ComplexNode):
    def emit(self, emitter):
        emitter.write('/* generated by esotope-bfc */')
        emitter.write('#include <stdio.h>')
        emitter.write('char mem[30000], *mptr = mem;')
        emitter.write('int main(void) {')
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.write('return 0;')
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'Program[%s]' % ComplexNode.__repr__(self)[1:-1]

class Nop(Node):
    def __nonzero__(self):
        return False

    def emit(self, emitter):
        pass

    def __repr__(self):
        return 'Nop[]'

class SetMemory(Node):
    def __init__(self, offset, value):
        self.offset = offset
        self.value = Expr(value)

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset
        self.value = self.value.movepointer(offset)

    def references(self):
        return self.value.references()

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        emitter.write('mptr[%d] = %s;' % (self.offset, self.value))

    def __repr__(self):
        return '%d=%r' % (self.offset, self.value)

class AdjustMemory(Node):
    def __init__(self, offset, delta):
        self.offset = offset
        self.delta = Expr(delta)

    def __nonzero__(self):
        return self.delta != 0

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset
        self.delta = self.delta.movepointer(offset)

    def references(self):
        return set([self.offset]) | self.delta.references()

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        if self.delta < 0:
            emitter.write('mptr[%d] -= %s;' % (self.offset, -self.delta))
        elif self.delta != 0:
            emitter.write('mptr[%d] += %s;' % (self.offset, self.delta))

    def __repr__(self):
        if self.delta < 0:
            return '%d-=%r' % (self.offset, -self.delta)
        else:
            return '%d+=%r' % (self.offset, self.delta)

class MovePointer(Node):
    def __init__(self, offset):
        self.offset = offset

    def __nonzero__(self):
        return self.offset != 0

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        pass # no change

    def offsets(self):
        return self.offset

    def emit(self, emitter):
        if self.offset < 0:
            emitter.write('mptr -= %s;' % -self.offset)
        elif self.offset != 0:
            emitter.write('mptr += %s;' % self.offset)

    def __repr__(self):
        return '@%r' % self.offset

class Input(Node):
    def __init__(self, offset):
        self.offset = offset

    def pure(self):
        return False

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        emitter.write('mptr[%s] = getchar();' % self.offset)

    def __repr__(self):
        return 'Input[%r]' % self.offset

class Output(Node):
    def __init__(self, expr):
        self.expr = expr

    def pure(self):
        return False

    def canmovepointer(self, offset):
        return True

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        self.expr = self.expr.movepointer(offset)

    def emit(self, emitter):
        emitter.write('putchar(%s);' % self.expr)

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

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        pass # does nothing

    def emit(self, emitter):
        for line in self.str.splitlines(True):
            emitter.write('printf("%s");' % _addslashes(line))

    def __repr__(self):
        return 'OutputConst[%r]' % self.str

class If(ComplexNode):
    def __init__(self, target, children=[]):
        ComplexNode.__init__(self, children)
        self.target = target

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.target += offset

    def offsets(self):
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return set([self.target]) | ComplexNode.references(self)

    def updates(self):
        return set([self.target]) | ComplexNode.updates(self)

    def emit(self, emitter):
        emitter.write('if (mptr[%s]) {' % self.target)
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'If[%r; %s]' % (self.target, ComplexNode.__repr__(self)[1:-1])

class LoopWhile(ComplexNode):
    def __init__(self, target, children=[]):
        ComplexNode.__init__(self, children)
        self.target = target

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.target += offset

    def offsets(self):
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return set([self.target]) | ComplexNode.references(self)

    def updates(self):
        return set([self.target]) | ComplexNode.updates(self)

    def emit(self, emitter):
        emitter.write('while (mptr[%s]) {' % self.target)
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'LoopWhile[%r; %s]' % (self.target, ComplexNode.__repr__(self)[1:-1])


class Emitter(object):
    def __init__(self):
        self.nindents = 0

    def write(self, line):
        print '\t' * self.nindents + line

    def indent(self):
        self.nindents += 1

    def dedent(self):
        self.nindents -= 1

class Compiler(object):
    def parse(self, fp):
        nodestack = [Program()]

        def flush(parent, changes, offset):
            for k, v in changes.items():
                if v != 0: parent.append(AdjustMemory(k, v))
            if offset != 0: parent.append(MovePointer(offset))

        changes = {}
        offset = 0
        for lineno, line in enumerate(fp):
            for ch in line:
                if ch == '+':
                    changes[offset] = changes.get(offset, 0) + 1
                elif ch == '-':
                    changes[offset] = changes.get(offset, 0) - 1
                elif ch == '>':
                    offset += 1
                elif ch == '<':
                    offset -= 1
                elif ch in '.,[]':
                    flush(nodestack[-1], changes, offset)
                    changes = {}
                    offset = 0

                    if ch == '.':
                        nodestack[-1].append(Output(Expr[0]))
                    elif ch == ',':
                        nodestack[-1].append(Input(0))
                    elif ch == '[':
                        nodestack.append(LoopWhile(0))
                    else:
                        if len(nodestack) < 2:
                            raise ValueError('Not matching ] at line %d' % (lineno+1))
                        loop = nodestack.pop()
                        nodestack[-1].append(loop)

        flush(nodestack[-1], changes, offset)
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    # minimizes number of MovePointer nodes.
    def optimize_minptrmoves(self, node):
        if not isinstance(node, ComplexNode):
            return node

        i = 0
        offset = 0
        while i < len(node):
            cur = node[i]
            if not cur: # remove no-op
                del node[i]
                continue

            if isinstance(cur, MovePointer):
                offset += cur.offset
                del node[i]
                continue
            else:
                if cur.canmovepointer(offset):
                    cur.movepointer(offset)
                else:
                    # movepointer failed, flush current MovePointer node before it
                    if offset != 0:
                        node.insert(i, MovePointer(offset))
                        i += 1
                    offset = 0
                node[i] = self.optimize_minptrmoves(cur)

            i += 1

        if offset != 0:
            node.append(MovePointer(offset))
        return node

    # change first AdjustMemory nodes to SetMemory in the very first of program.
    # also removes the last (redundant) MovePointer if any.
    def optimize_onceuponatime(self, node):
        if not isinstance(node, Program):
            return node

        i = 0
        offsets = 0
        changed = set()
        while i < len(node):
            if isinstance(node[i], AdjustMemory) and \
                    node[i].offset + offsets not in changed:
                node[i] = SetMemory(node[i].offset, node[i].delta)
            elif isinstance(node[i], (LoopWhile, If)) and \
                    node[i].target + offsets not in changed:
                node[i] = Nop() # effectively no-op

            ioffsets = node[i].offsets()
            if ioffsets is None: break
            offsets += ioffsets

            changed.update(j + offsets for j in node[i].updates() if j is not None)
            i += 1

        while node and isinstance(node[-1], MovePointer):
            del node[-1]
        return node

    # tries to optimize tight loop: LoopWhile[0+=1/0-=1, ...] w/o any MovePointers.
    # every value of memory ops should be simple expression such as 4 or -3.
    def optimize_tightloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 256 # XXX hard-coded, must be the power of 2

        inodes = []
        for inode in node:
            if isinstance(inode, LoopWhile) and inode.offsets() == 0 and inode.pure():
                # check constraints.
                current = 0
                currentset = False
                hasset = False
                multiplier = None
                for change in inode:
                    if isinstance(change, SetMemory):
                        if not change.value.simple(): break
                        if change.offset == inode.target:
                            current = change.value
                            currentset = True
                        hasset = True # in this case we should use If[] instead.
                    elif isinstance(change, AdjustMemory):
                        if not change.delta.simple(): break
                        if change.offset == inode.target:
                            current += change.delta
                    elif isinstance(change, ComplexNode):
                        break
                else:
                    if currentset:
                        if current == 0:
                            multiplier = 1
                    else:
                        if current == 1:
                            multiplier = overflow - Expr[inode.target]
                        elif current == -1:
                            multiplier = Expr[inode.target]

                if multiplier is not None:
                    if hasset:
                        changes = []
                    else:
                        changes = inodes

                    for change in inode:
                        if change.offset == inode.target: continue
                        if isinstance(change, AdjustMemory):
                            change.delta *= multiplier
                        changes.append(change)

                    if hasset:
                        inodes.append(If(inode.target, changes))
                    inodes.append(SetMemory(inode.target, 0))
                    continue

            if isinstance(inode, ComplexNode):
                inodes.append(self.optimize_tightloop(inode))
            else:
                inodes.append(inode)

        node[:] = inodes
        return node

    # propagates cell references and constants as much as possible.
    # requires minptrloops pass for optimal processing. otherwise MovePointer
    # will act as memory blocker.
    def optimize_propagate(self, node):
        if not isinstance(node, ComplexNode):
            return node

        backrefs = {}
        usedrefs = {}
        substs = {} # only for simple one, unless some vars are not current

        i = 0
        while i < len(node):
            cur = node[i]

            impure = mergable = False
            offset = None
            refs = []
            if isinstance(cur, SetMemory):
                impure = mergable = True
                offset = cur.offset
                value = cur.value = cur.value.withmemory(substs)
                refs = value.references()
                if value.simple():
                    substs[offset] = value
                else:
                    try: del substs[offset]
                    except: pass
            elif isinstance(cur, AdjustMemory):
                impure = mergable = True
                offset = cur.offset
                delta = cur.delta = cur.delta.withmemory(substs)
                refs = delta.references()
                if offset in substs:
                    substs[offset] += delta
                    if substs[offset].simple():
                        # replace with equivalent SetMemory node.
                        cur = node[i] = SetMemory(offset, substs[offset])
                    else:
                        del substs[offset]
            elif isinstance(cur, Input):
                impure = True
                offset = cur.offset
                try: del substs[offset]
                except: pass
            elif isinstance(cur, Output):
                expr = cur.expr = cur.expr.withmemory(substs)
                refs = expr.references()
            else: # MovePointer, LoopWhile etc.
                node[i] = self.optimize_propagate(cur)
                backrefs.clear()
                usedrefs.clear()
                substs.clear()
                if isinstance(cur, (LoopWhile, If)):
                    substs[cur.target] = Expr()

            merged = False
            if impure:
                if not mergable:
                    # prohibit next merging attempt.
                    try: del backrefs[offset]
                    except: pass
                elif offset in backrefs:
                    # we can merge changes[target] and changes[i] if:
                    # - no operation has changed cell k between them. (thus such target
                    #   is backrefs[offset], as it is updated after change)
                    # - no operation has referenced cell k between them. it includes
                    #   changes[target] which is self-reference (like a = a + 4).
                    # - no operation has changed cell k' which is referenced by v.
                    #   it includes changes[target] too, if v references targetous k.
                    target = backrefs[offset]
                    if target > usedrefs.get(offset, -1) and \
                            all(target > backrefs.get(ioffset, -1) for ioffset in refs):
                        if isinstance(cur, SetMemory):
                            node[target] = SetMemory(offset, cur.value)
                        elif isinstance(node[target], SetMemory):
                            node[target].value += cur.delta
                        else:
                            node[target].delta += cur.delta
                        del node[i]
                        merged = True
                    else:
                        backrefs[offset] = i
                else:
                    backrefs[offset] = i

            if not merged:
                target = i
                i += 1
            for ioffset in refs:
                usedrefs[ioffset] = target

        return node

    # extensive loop optimization. it calculates repeat count if possible and
    # tries to convert them into For[].
    def optimize_loop(self, node):
        pass

    # converts common idioms to direct C library call.
    def optimize_stdlib(self, node):
        if not isinstance(node, ComplexNode):
            return node

        inodes = []
        laststr = []
        for inode in node:
            if isinstance(inode, Output) and inode.expr.simple():
                laststr.append(chr(int(inode.expr) & 0xff))
            elif isinstance(inode, OutputConst):
                laststr.append(inode.str)
            elif isinstance(inode, (Input, SetMemory, AdjustMemory, MovePointer)):
                inodes.append(inode) # doesn't affect string output
            else:
                if laststr:
                    inodes.append(OutputConst(''.join(laststr)))
                    laststr = []
                if isinstance(inode, ComplexNode):
                    inodes.append(self.optimize_stdlib(inode))
                else:
                    inodes.append(inode)
        if laststr:
            inodes.append(OutputConst(''.join(laststr)))
        node[:] = inodes
        return node

def main(argv):
    if len(argv) < 2:
        print >>sys.stderr, 'Usage: %s filename' % argv[0]
        return 1

    compiler = Compiler()
    node = compiler.parse(file(argv[1], 'r'))
    node = compiler.optimize_tightloop(node)
    node = compiler.optimize_minptrmoves(node)
    node = compiler.optimize_onceuponatime(node)
    node = compiler.optimize_propagate(node)
    node = compiler.optimize_tightloop(node)
    node = compiler.optimize_propagate(node)
    node = compiler.optimize_stdlib(node)
    node.emit(Emitter())
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

