# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.parser.base import BaseParser

class Parser(BaseParser):
    """The run-length encoded Brainfuck parser. (As emitted by gcc-bf)

    Basically, this is a simple extension to Brainfuck language adding "+*xx",
    "-*xx", ">*xx" and "<*xx" shortcuts. xx should be the positive, non-zero
    number, and otherwise * is treated as comment.
    """

    def parse(self, fp):
        nodestack = [Program()]
        offsetstack = [0]

        for lineno, line in enumerate(fp):
            i = 0
            lline = len(line)
            while i < lline:
                ch = line[i]
                i += 1

                if ch in '+-><':
                    # detect +*xx form.
                    if i + 1 < lline and line[i] == '*' and '1' <= line[i+1] <= '9':
                        nexti = i + 2
                        while nexti < lline and '0' <= line[nexti] <= '9':
                            nexti += 1
                        repcount = int(line[i+1:nexti])
                        i = nexti
                    else:
                        repcount = 1

                    if ch == '+':
                        nodestack[-1].append(AdjustMemory(0, +repcount))
                    elif ch == '-':
                        nodestack[-1].append(AdjustMemory(0, -repcount))
                    elif ch == '>':
                        nodestack[-1].append(MovePointer(+repcount))
                    else: # ch == '<'
                        nodestack[-1].append(MovePointer(-repcount))

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

