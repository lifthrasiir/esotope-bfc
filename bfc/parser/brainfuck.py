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
        nodestack = [Program()]
        offsetstack = [0]

        repch = ''
        repcount = 0
        for lineno, line in enumerate(fp):
            for ch in line:
                if ch == repch:
                    repcount += 1
                else:
                    # merge repeated operations. this is only basic optimization,
                    # and doesn't account for +- or >< sequences. flatten pass is
                    # used for that.
                    #
                    # the rationale behind this is to preserve the original code
                    # as much as possible while limiting the memory usage. you can
                    # recover the original code without comments quickly: for
                    # example, MovePointer[+3] represents >>> and MovePointer[-2]
                    # represents <<. even >>><< is represented with two nodes.

                    if repcount > 0:
                        if repch == '+':
                            nodestack[-1].append(AdjustMemory(0, +repcount))
                        elif repch == '-':
                            nodestack[-1].append(AdjustMemory(0, -repcount))
                        elif repch == '>':
                            nodestack[-1].append(MovePointer(+repcount))
                        elif repch == '<':
                            nodestack[-1].append(MovePointer(-repcount))

                    repch = ''
                    if ch in '+-><':
                        repch = ch
                        repcount = 1
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

        if repcount > 0:
            if repch == '+':
                nodestack[-1].append(AdjustMemory(0, +repcount))
            elif repch == '-':
                nodestack[-1].append(AdjustMemory(0, -repcount))
            elif repch == '>':
                nodestack[-1].append(MovePointer(+repcount))
            elif repch == '<':
                nodestack[-1].append(MovePointer(-repcount))

        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    def unknown(self, ch, nodestack):
        pass

