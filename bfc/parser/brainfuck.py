# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.parser.base import BaseParser

class Parser(BaseParser):
    """The basic Brainfuck parser.

    It handles eight basic Brainfuck commands, and calls the handler for unknown
    character. Basically unknown handler does nothing, but one can handle other
    commands (like #) via subclassing.
    """

    def parse(self, fp):
        """Creates the Program node corresponding to the given program.
        Unmatched bracket is checked, and all non-command character is ignored.
        (`#`, `!` or similar things are not supported yet.)

        This method tries to generate the smaller node as much as possible. All
        memory operation is pointer-propagated, and almost all pointer operation
        is vanished (except for one at the very end of loop).
        """

        nodestack = [Program()]
        offsetstack = [0]

        for lineno, line in enumerate(fp):
            for ch in line:
                if ch == '+':
                    nodestack[-1].append(AdjustMemory(0, +1))
                elif ch == '-':
                    nodestack[-1].append(AdjustMemory(0, -1))
                elif ch == '>':
                    nodestack[-1].append(MovePointer(+1))
                elif ch == '<':
                    nodestack[-1].append(MovePointer(-1))
                elif ch == '.':
                    nodestack[-1].append(Output(Expr[0]))
                elif ch == ',':
                    nodestack[-1].append(Input(0))
                elif ch == '[':
                    nodestack.append(While(MemNotEqual(0, 0)))
                elif ch == ']':
                    if len(nodestack) < 2:
                        raise ValueError('Not matching ] at line %d' % (lineno+1))
                    loop = nodestack.pop()
                    nodestack[-1].append(loop)
                else:
                    self.unknown(ch, nodestack)

        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    def unknown(self, ch, nodestack):
        pass

