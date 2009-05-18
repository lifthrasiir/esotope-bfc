# This is a part of Esotope Brainfuck-to-C Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt import initialmemory, propagate, removedead, simpleloop, stdlib
from bfc.codegen import c as codegen_c

class Compiler(object):
    def __init__(self, cellsize=8, debugging=False):
        self.cellsize = cellsize
        self.optpasses = [
            simpleloop.SimpleLoopPass,
            initialmemory.InitialMemoryPass,
            propagate.PropagatePass,
            simpleloop.SimpleLoopPass,
            propagate.PropagatePass,
            removedead.RemoveDeadPass,
            stdlib.StdlibPass,
        ]
        self.codegen = codegen_c.CGenerator
        self.debugging = debugging

    def parse(self, fp):
        nodestack = [Program()]
        offsetstack = [0]

        changes = {}
        offset = offsetbase = 0
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
                    for k, v in changes.items():
                        if v != 0: nodestack[-1].append(AdjustMemory(k, v))
                    changes = {}

                    if ch == '.':
                        nodestack[-1].append(Output(Expr[offset]))
                    elif ch == ',':
                        nodestack[-1].append(Input(offset))
                    elif ch == '[':
                        nodestack.append(While(MemNotEqual(offset, 0)))
                        offsetstack.append(offsetbase)
                        offsetbase = offset
                    else: # ch == ']'
                        if len(nodestack) < 2:
                            raise ValueError('Not matching ] at line %d' % (lineno+1))
                        if offset != offsetbase: # unbalanced loop
                            nodestack[-1].append(MovePointer(offset - offsetbase))

                        offset = offsetbase
                        loop = nodestack.pop()
                        offsetbase = offsetstack.pop()
                        nodestack[-1].append(loop)

        for k, v in changes.items():
            if v != 0: nodestack[-1].append(AdjustMemory(k, v))
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    # calls given function with all nodes within node recursively,
    # in the reverse order of depth-first search.
    def visit(self, node, func):
        visit = self.visit
        for inode in node:
            if isinstance(inode, ComplexNode): visit(inode, func)
        return func(node)

    def optimize(self, node):
        for passcls in self.optpasses:
            passobj = passcls(self)
            # TODO passobj.check is not used yet.
            node = passobj.transform(node)
        return node

    def generate(self, node):
        gen = self.codegen(self)
        gen.generate(node)
        gen.flush()
        return gen

    def compile(self, fp):
        node = self.parse(fp)
        node = self.optimize(node)
        return self.generate(node)

