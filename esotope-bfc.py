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

    class Add(namedtuple('Add', 'lhs rhs'), _exprbase):
        def __str__(self): return '(%s + %s)' % (self.lhs, self.rhs)
        def __repr__(self): return '(%r+%r)' % (self.lhs, self.rhs)
        def apply(self, func, merge=None):
            return (merge or Expr.Add)(self.lhs.apply(func, merge),
                    self.rhs.apply(func, merge))

    class Subtract(namedtuple('Subtract', 'lhs rhs'), _exprbase):
        def __str__(self): return '(%s - %s)' % (self.lhs, self.rhs)
        def __repr__(self): return '(%r-%r)' % (self.lhs, self.rhs)
        def apply(self, func, merge=None):
            return (merge or Expr.Subtract)(self.lhs.apply(func, merge),
                    self.rhs.apply(func, merge))

    class Multiply(namedtuple('Multiply', 'lhs rhs')):
        def __str__(self): return '(%s * %s)' % (self.lhs, self.rhs)
        def __repr__(self): return '(%r*%r)' % (self.lhs, self.rhs)
        def apply(self, func, merge=None):
            return (merge or Expr.Multiply)(self.lhs.apply(func, merge),
                    self.rhs.apply(func, merge))

    def __init__(self, obj=0):
        if isinstance(obj, (int, long)):
            self.root = Expr.Number(obj)
        elif isinstance(obj, Expr):
            self.root = obj.root
        else:
            self.root = obj

    def __neg__(self):
        return Expr(Expr.Negate(self.root))

    def __pos__(self):
        return self

    def __add__(self, rhs):
        if rhs == 0: return self
        return Expr(Expr.Add(self.root, Expr(rhs).root))

    def __radd__(self, lhs):
        if lhs == 0: return self
        return Expr(Expr.Add(Expr(lhs).root, self.root))

    def __sub__(self, rhs):
        if rhs == 0: return self
        return Expr(Expr.Subtract(self.root, Expr(rhs).root))

    def __rsub__(self, lhs):
        if lhs == 0: return -self
        return Expr(Expr.Subtract(Expr(lhs).root, self.root))

    def __mul__(self, rhs):
        if rhs == 0: return Expr()
        if rhs == 1: return self
        if rhs == -1: return -self
        return Expr(Expr.Multiply(self.root, Expr(rhs).root))

    def __rmul__(self, lhs):
        if lhs == 0: return Expr()
        if lhs == 1: return self
        if lhs == -1: return -self
        return Expr(Expr.Multiply(Expr(lhs).root, self.root))

    def __eq__(self, rhs): return self.root == Expr(rhs).root
    def __ne__(self, rhs): return self.root != Expr(rhs).root

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

    def cleanup(self):
        i = 1
        while i < len(self):
            if not self[i-1]:
                del self[i-1]
            else:
                combined = self[i-1].combine(self[i])
                if combined is not None:
                    self[i-1] = combined
                    del self[i]
                else:
                    i += 1
        if self and not self[0]:
            del self[0]

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

class MemoryOps(Node, list):
    def __init__(self, offset=0, changes=None):
        self.offset = offset
        try:
            self.changes = [(k, False, v) for k, v in changes.items()]
        except:
            self.changes = changes or []

    def __nonzero__(self):
        return len(self.changes) > 0 or self.offset != 0

    def get(self, offset):
        value = Expr[offset]
        for k, set, v in self.changes:
            if k == offset:
                if set: value = v
                else: value += v
        return value

    def set(self, offset, value):
        self.changes.append((offset, False, value))

    def adjust(self, offset, delta):
        if delta != 0:
            self.changes.append((offset, True, delta))

    def combine(self, next):
        if isinstance(next, MemoryOps):
            offset = self.offset
            for k, set, v in next.changes:
                self.changes.append((offset + k, set, v.movepointer(offset)))
            self.offset += next.offset
            return self

    def __str__(self):
        codes = []

        for k, set, v in self.changes:
            if set:
                codes.append('mptr[%d] = %s;\n' % (k, v))
            elif v < 0:
                codes.append('mptr[%d] -= %s;\n' % (k, -v))
            elif v != 0:
                codes.append('mptr[%d] += %s;\n' % (k, v))

        if self.offset < 0:
            codes.append('mptr -= %s;\n' % -self.offset)
        elif self.offset != 0:
            codes.append('mptr += %s;\n' % self.offset)

        return ''.join(codes)

    def __repr__(self):
        items = []
        for k, set, v in sorted(self.changes.items()):
            if set:
                items.append('%d=%s' % (k, v))
            elif v < 0:
                items.append('%d+=%s' % (k, v))
            elif v != 0:
                items.append('%d-=%s' % (k, v))
        if self.offset != 0:
            items.append('offset=%r' % self.offset)
        return 'MemoryOps[%s]' % ', '.join(items)

class Input(Node):
    def __str__(self):
        return '*mptr = getchar();\n'

    def __repr__(self):
        return 'Input[]'

class Output(Node):
    def __str__(self):
        return 'putchar(*mptr);\n'

    def __repr__(self):
        return 'Output[]'

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
                    if offset != 0 or any(changes.values()):
                        nodestack[-1].append(MemoryOps(offset, changes))
                    changes = {}
                    offset = 0

                    if ch == '.':
                        nodestack[-1].append(Output())
                    elif ch == ',':
                        nodestack[-1].append(Input())
                    elif ch == '[':
                        nodestack.append(LoopWhile())
                    else:
                        if len(nodestack) < 2:
                            raise ValueError('Not matching ] at line %d' % (lineno+1))
                        loop = nodestack.pop()
                        nodestack[-1].append(loop)

        if offset != 0 or any(changes.values()):
            nodestack[-1].append(MemoryOps(offset, changes))
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')

        return nodestack[0]

    # tries to optimize tight loop: LoopWhile[MemoryOps[0+=1/0-=1, ..., offset=0]].
    def optimize_tightloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 256 # XXX hard-coded, must be the power of 2

        inodes = []
        for inode in node[:]:
            if isinstance(inode, LoopWhile) and len(inode) == 1 and \
                    isinstance(inode[0], MemoryOps) and inode[0].offset == 0:
                adjustnode = inode[0]
                if adjustnode[0] == 1:
                    mult = overflow - Expr[0]
                elif adjustnode[0] == -1:
                    mult = Expr[0]
                else:
                    mult = None

                if mult is not None:
                    adjustnode[0] = 0
                    for k in adjustnode.changes.keys():
                        adjustnode[k] *= mult
                    inodes.append(adjustnode)
                    inodes.append(SetCurrent(0))
                    continue

            if isinstance(inode, ComplexNode):
                inodes.append(self.optimize_tightloop(inode))
            else:
                inodes.append(inode)

        node[:] = inodes
        node.cleanup()
        return node

def main(argv):
    if len(argv) < 2:
        print >>sys.stderr, 'Usage: %s filename' % argv[0]
        return 1

    compiler = Compiler()
    node = compiler.parse(file(argv[1], 'r'))
    #node = compiler.optimize_tightloop(node)
    print node
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

