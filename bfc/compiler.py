# This is a part of Esotope Brainfuck compiler.

"""The compiler class.

This class provides the basic interface to parser, optimizer and code
generator. If you are not interested in the internal workings, Compiler
class should be sufficient.
"""

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt import initialmemory, propagate, removedead, simpleloop, stdlib
from bfc.codegen import c as codegen_c

class Compiler(object):
    """Compiler class. It provides the optimizing parser (via parse method),
    and abstracts the optimizer passes and code generators."""

    def __init__(self, cellsize=8, debugging=False):
        """Compiler(cellsize=8, debugging=False) -> Compiler object

        Creates Compiler object with given Brainfuck environment. cellsize
        should be 8 (default), 16 or 32. debugging can be set to True in order
        to generate more verbose output."""

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
        """compiler.parse(filelike) -> Program node

        Creates the Program node corresponding to the given program. Unmatched
        bracket is checked, and all non-command character is ignored. (`#`, `!`
        or similar things are not supported yet.)

        This method tries to generate the smaller node as much as possible. All
        memory operation is pointer-propagated, and almost all pointer operation
        is vanished (except for one at the very end of loop).
        """

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

    def visit(self, node, func):
        """compiler.visit(node, func) -> anything

        It calls given function with all nodes within given node recursively,
        in the reverse order of depth-first search. (i.e. visit children first
        and visit root later)
        """

        visit = self.visit
        for inode in node:
            if isinstance(inode, ComplexNode): visit(inode, func)
        return func(node)

    def optimize(self, node):
        """compiler.optimize(node) -> node

        Optimizes the given node using internal optimizer passes. You can
        provide additional passes by appending the class to compiler.optpasses.
        The node could be modified in-place.
        """

        for passcls in self.optpasses:
            passobj = passcls(self)
            # TODO passobj.check is not used yet.
            node = passobj.transform(node)
        return node

    def generate(self, node):
        """compiler.generate(node) -> Generator

        Creates the instance of current code generator, and feeds the given node
        to that generator. (It calls flush method so normally everything is
        printed out. Returns the new code generator object."""

        gen = self.codegen(self)
        gen.generate(node)
        gen.flush()
        return gen

    def compile(self, fp):
        """compiler.compile(filelike) -> Generator

        One-shot shortcut for parse, optimization and code generation. It reads
        the source code, optimizes it and generates the output via the current
        code generator."""

        node = self.parse(fp)
        node = self.optimize(node)
        return self.generate(node)

