#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
from collections import namedtuple
from cStringIO import StringIO


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


def insert_indent(s):
    if s == '': return s
    return '\t' + s.rstrip('\n').replace('\n', '\n\t') + '\n'

class Node(object):
    def __nonzero__(self):
        return True # ... or return False if this node is no-op.

    def offsets(self):
        return 0

    def changes(self):
        return {}

    def __str__(self): raise NotImplemented('should be overriden')
    def __repr__(self): raise NotImplemented('should be overriden')

class IONode(Node):
    pass

class ComplexNode(Node, list):
    def __nonzero__(self):
        return len(self) > 0

    def _indentall(self):
        return ''.join(map(insert_indent, map(str, self)))

    def _repr(self, name):
        return name + list.__repr__(self)

    def pure(self, start=None, end=None):
        for i in xrange(*slice(start, end).indices(len(self))):
            if isinstance(self[i], IONode): return False
        return True

    def offsets(self, start=None, end=None):
        offsets = 0
        for i in xrange(*slice(start, end).indices(len(self))):
            offsets += self[i].offsets()
        return offsets

    # XXX
    def changes(self, start=None, end=None):
        offsets = 0
        changes = {}
        for i in xrange(*slice(start, end).indices(len(self))):
            ichanges = self[i].changes()
            changes.update((k + offsets, v.movepointer(offsets)) for k, v in ichanges.items())
            offsets += self[i].offsets()
        return changes

class Program(ComplexNode):
    def __str__(self):
        return ('/* generated by esotope-bfc */\n'
                '#include <stdio.h>\n'
                'char mem[30000], *mptr = mem;\n'
                'int main(void) {\n'
                '%s'
                '\treturn 0;\n'
                '}\n') % self._indentall()

    def __repr__(self):
        return self._repr('Program')

class SetMemory(Node):
    def __init__(self, offset, value):
        self.offset = offset
        self.value = Expr(value)

    def movepointer(self, offset):
        self.offset += offset
        self.value = self.value.movepointer(offset)

    def changes(self):
        return {self.offset: self.value}

    def __str__(self):
        return 'mptr[%d] = %s;\n' % (self.offset, self.value)

    def __repr__(self):
        return '%d=%r' % (self.offset, self.value)

class AdjustMemory(Node):
    def __init__(self, offset, delta):
        self.offset = offset
        self.delta = Expr(delta)

    def __nonzero__(self):
        return self.delta != 0

    def movepointer(self, offset):
        self.offset += offset
        self.delta = self.delta.movepointer(offset)

    def changes(self):
        return {self.offset: Expr[self.offset] + self.delta}

    def __str__(self):
        if self.delta < 0:
            return 'mptr[%d] -= %s;\n' % (self.offset, -self.delta)
        elif self.delta != 0:
            return 'mptr[%d] += %s;\n' % (self.offset, self.delta)
        else:
            return ''

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

    def offsets(self):
        return self.offset

    def __str__(self):
        if self.offset < 0:
            return 'mptr -= %s;\n' % -self.offset
        elif self.offset != 0:
            return 'mptr += %s;\n' % self.offset
        else:
            return ''

    def __repr__(self):
        return '@%r' % self.offset

class Input(IONode):
    def __init__(self, offset):
        self.offset = offset

    def movepointer(self, offset):
        self.offset += offset

    def changes(self):
        return {self.offset: None}

    def __str__(self):
        return 'mptr[%s] = getchar();\n' % self.offset

    def __repr__(self):
        return 'Input[%r]' % self.offset

class Output(IONode):
    def __init__(self, expr):
        self.expr = expr

    def movepointer(self, offset):
        self.expr = self.expr.movepointer(offset)

    def __str__(self):
        return 'putchar(%s);\n' % self.expr

    def __repr__(self):
        return 'Output[%r]' % self.expr

class If(ComplexNode):
    def __str__(self):
        return ('if (*mptr) {\n'
                '%s'
                '}\n') % self._indentall()

    def __repr__(self):
        return self._repr('If')

class LoopWhile(ComplexNode):
    def __str__(self):
        return ('while (*mptr) {\n'
                '%s'
                '}\n') % self._indentall()

    def __repr__(self):
        return self._repr('LoopWhile')


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
                        nodestack.append(LoopWhile())
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

            if isinstance(cur, (SetMemory, AdjustMemory, Input, Output)):
                cur.movepointer(offset)
            elif isinstance(cur, MovePointer):
                offset += cur.offset
                del node[i]
                continue
            else: # e.g. LoopWhile
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
        changed = set()
        while i < len(node):
            if isinstance(node[i], (SetMemory, Input)):
                changed.add(node[i].offset)
            elif isinstance(node[i], AdjustMemory):
                if node[i].offset not in changed:
                    node[i] = SetMemory(node[i].offset, node[i].delta)
                changed.add(node[i].offset)
            elif not isinstance(node[i], Output):
                break
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
        for inode in node[:]:
            if isinstance(inode, LoopWhile) and inode.offsets() == 0 and inode.pure():
                # check constraints.
                current = 0
                currentset = False
                hasset = False
                multiplier = None
                for change in inode:
                    if isinstance(change, SetMemory):
                        if not change.value.simple(): break
                        if change.offset == 0:
                            current = change.value
                            currentset = True
                        hasset = True # in this case we should use If[] instead.
                    elif isinstance(change, AdjustMemory):
                        if not change.delta.simple(): break
                        if change.offset == 0:
                            current += change.delta
                    elif isinstance(change, ComplexNode):
                        break
                else:
                    if currentset:
                        if current == 0:
                            multiplier = 1
                    else:
                        if current == 1:
                            multiplier = overflow - Expr[0]
                        elif current == -1:
                            multiplier = Expr[0]

                if multiplier is not None:
                    if hasset:
                        changes = []
                    else:
                        changes = inodes

                    for change in inode:
                        if change.offset == 0: continue
                        if isinstance(change, AdjustMemory):
                            change.delta *= multiplier
                        changes.append(change)

                    if hasset:
                        inodes.append(If(changes))
                    inodes.append(SetMemory(0, 0))
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
                    substs[0] = Expr()

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
    print node
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

