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
        def apply(self, func, merge=None): return func(self)

    class MemoryRef(namedtuple('MemoryRef', 'offset'), _exprbase):
        def __str__(self): return 'mptr[%s]' % self.offset
        def __repr__(self): return 'mptr[%r]' % self.offset
        def apply(self, func, merge=None): return func(self)

    class Negate(namedtuple('Negate', 'expr'), _exprbase):
        def __str__(self): return '-%s' % (self.expr,)
        def __repr__(self): return '-%r' % (self.expr,)
        def apply(self, func, merge=None):
            return (merge or Expr.Negate)(self.expr.apply(func, merge))

    class Sum(_exprbase):
        def _prettify(self, func):
            items = [func(self[0])]
            for child in self[1:]:
                if isinstance(child, Expr.Negate):
                    items.extend(['-', func(child.expr)])
                else:
                    items.extend(['+', func(child)])
            return items

        def __str__(self): return '(%s)' % ' '.join(self._prettify(str))
        def __repr__(self): return '(%s)' % ''.join(self._prettify(repr))
        def apply(self, func, merge=None):
            return (merge or Expr.Sum)(*[i.apply(func, merge) for i in self])

    class Product(_exprbase):
        def __str__(self): return '(%s)' % ' * '.join(map(str, self))
        def __repr__(self): return '(%s)' % '*'.join(map(repr, self))
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
        if lhs == 0: return rhs
        if rhs == 0: return lhs
        if isinstance(lhs.root, Expr.Number) and isinstance(rhs.root, Expr.Number):
            return Expr(lhs.root.value + rhs.root.value)
        return Expr(Expr.Sum(lhs.root, Expr(rhs).root))

    def __radd__(rhs, lhs): return Expr(lhs) + rhs
    def __sub__(lhs, rhs): return lhs + (-rhs)
    def __rsub__(rhs, lhs): return lhs + (-rhs)

    def __mul__(lhs, rhs):
        if lhs == 0 or rhs == 0: return Expr()
        if lhs == 1: return rhs
        if rhs == 1: return lhs
        if lhs == -1: return -rhs
        if rhs == -1: return -lhs
        if isinstance(lhs.root, Expr.Number) and isinstance(rhs.root, Expr.Number):
            return Expr(lhs.root.value * rhs.root.value)
        return Expr(Expr.Product(lhs.root, Expr(rhs).root))

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

    def setmemory(self, map):
        def func(node):
            if not isinstance(node, Expr.MemoryRef): return node
            return map.get(node.offset, node)
        return Expr(self.root.apply(func))

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

    def combine(self, next):
        return None # ... or return combined Node object.

    def __str__(self): raise NotImplemented('should be overriden')
    def __repr__(self): raise NotImplemented('should be overriden')

class ComplexNode(Node, list):
    def _indentall(self):
        return ''.join(map(insert_indent, map(str, self)))

    def _repr(self, name):
        return name + list.__repr__(self)

    def pure(self, start=None, end=None):
        for i in xrange(*slice(start, end).indices(len(self))):
            if isinstance(self[i], (Input, Output)): return False
        return True

    def offset(self, start=None, end=None):
        offset = 0
        for i in xrange(*slice(start, end).indices(len(self))):
            if isinstance(self[i], MovePointer):
                offset += self[i].offset
        return offset

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

    def __str__(self):
        if self.offset < 0:
            return 'mptr -= %s;\n' % -self.offset
        elif self.offset != 0:
            return 'mptr += %s;\n' % self.offset
        else:
            return ''

    def __repr__(self):
        return '@%r' % self.offset

class Input(Node):
    def __init__(self, offset):
        self.offset = offset

    def movepointer(self, offset):
        self.offset += offset

    def __str__(self):
        return 'mptr[%s] = getchar();\n' % self.offset

    def __repr__(self):
        return 'Input[%r]' % self.offset

class Output(Node):
    def __init__(self, offset):
        self.offset = offset

    def movepointer(self, offset):
        self.offset += offset

    def __str__(self):
        return 'putchar(mptr[%s]);\n' % self.offset

    def __repr__(self):
        return 'Output[%r]' % self.offset

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
                        nodestack[-1].append(Output(0))
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

    # tries to optimize tight loop: LoopWhile[0+=1/0-=1, ...] w/o any MovePointers.
    # every value of memory ops should be simple expression such as 4 or -3.
    def optimize_tightloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 256 # XXX hard-coded, must be the power of 2

        inodes = []
        for inode in node[:]:
            if isinstance(inode, LoopWhile) and inode.offset() == 0 and inode.pure():
                # check constraints.
                current = 0
                multiplier = None
                for change in inode:
                    if isinstance(change, SetMemory):
                        if not change.value.simple(): break
                        if change.offset == 0: break # XXX how to treat conditional?
                    elif isinstance(change, AdjustMemory):
                        if not change.delta.simple(): break
                        if change.offset == 0: current += change.delta
                    elif isinstance(change, ComplexNode):
                        break
                else:
                    if current == 1:
                        multiplier = overflow - Expr[0]
                    elif current == -1:
                        multiplier = Expr[0]

                if multiplier is not None:
                    for change in inode:
                        if change.offset == 0: continue
                        if isinstance(change, AdjustMemory):
                            change.delta *= multiplier
                        inodes.append(change)
                    inodes.append(SetMemory(0, 0))
                    continue

            if isinstance(inode, ComplexNode):
                inodes.append(self.optimize_tightloop(inode))
            else:
                inodes.append(inode)

        node[:] = inodes
        return node

    # dead code elimination and constant propagation.
    # TODO: should use better algorithm.
    def optimize_propagate(self, node):
        if not isinstance(node, ComplexNode):
            return node

        backrefs = {}
        usedrefs = {}

        i = 0
        poffset = 0
        while i < len(node):
            cur = node[i]

            impure = mergable = False
            offset = None
            refs = []
            if isinstance(cur, SetMemory):
                impure = mergable = True
                offset = poffset + cur.offset
                refs = [poffset + ref for ref in cur.value.references()]
            elif isinstance(cur, AdjustMemory):
                impure = mergable = True
                offset = cur.offset
                refs = [poffset + ref for ref in cur.delta.references()]
            elif isinstance(cur, MovePointer):
                poffset += cur.offset
            elif isinstance(cur, Input):
                impure = True
                offset = poffset + cur.offset
            elif isinstance(cur, Output):
                refs = [poffset + cur.offset]
            else:
                node[i] = self.optimize_propagate(cur)

                # invalidates all prior references.
                backrefs.clear()
                usedrefs.clear()
                poffset = 0

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
                            node[target] = cur
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
    node = compiler.optimize_minptrmoves(node)
    node = compiler.optimize_tightloop(node)
    node = compiler.optimize_minptrmoves(node)
    node = compiler.optimize_propagate(node)
    print node
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

