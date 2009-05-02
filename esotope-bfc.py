#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
from cStringIO import StringIO

def insert_indent(s):
    return '\t' + s.rstrip('\n').replace('\n', '\n\t') + '\n'

class Node(object):
    pass

class ComplexNode(Node):
    def __init__(self, children=None):
        if children:
            self.children = list(children)
        else:
            self.children = []

    def __getattr__(self, name):
        return getattr(self.children, name)

    def _indentall(self):
        return ''.join(map(insert_indent, map(str, self.children)))

class Node_Program(ComplexNode):
    def __str__(self):
        return ('/* generated by esotope-bfc */\n'
                '#include <stdio.h>\n'
                'char mem[30000], *mptr = mem;\n'
                'int main(void) {\n'
                '%s'
                '\treturn 0;\n'
                '}\n') % self._indentall()

    def __repr__(self):
        return 'Program%r' % self.children

class Node_MemDelta(Node):
    def __init__(self, delta):
        self.delta = delta

    def __str__(self):
        if self.delta < 0:
            return '*mptr -= %s;\n' % -self.delta
        elif self.delta != 0:
            return '*mptr += %s;\n' % self.delta

    def __repr__(self):
        return 'MemDelta[%r]' % self.delta

class Node_PtrDelta(Node):
    def __init__(self, delta):
        self.delta = delta

    def __str__(self):
        if self.delta < 0:
            return 'mptr -= %s;\n' % -self.delta
        elif self.delta != 0:
            return 'mptr += %s;\n' % self.delta

    def __repr__(self):
        return 'PtrDelta[%r]' % self.delta

class Node_Input(Node):
    def __str__(self):
        return '*mptr = getchar();\n'

    def __repr__(self):
        return 'Input[]'

class Node_Output(Node):
    def __str__(self):
        return 'putchar(*mptr);\n'

    def __repr__(self):
        return 'Output[]'

class Node_LoopWhile(ComplexNode):
    def __str__(self):
        return ('while (*mptr) {\n'
                '%s'
                '}\n') % self._indentall()

    def __repr__(self):
        return 'LoopWhile%r' % self.children

class Parser(object):
    def parse(self, fp):
        nodestack = [Node_Program()]

        lastmemdelta = 0
        lastptrdelta = 0
        for lineno, line in enumerate(fp):
            for ch in line:
                if ch not in '+-><.,[]': continue

                # simple optimization:
                # combine ++++ and ---- into one single memdelta node.
                # combine >>>> and <<<< into one single ptrdelta node.

                if ch not in '+-' and lastmemdelta != 0:
                    assert lastptrdelta == 0
                    nodestack[-1].append(Node_MemDelta(lastmemdelta))
                    lastmemdelta = 0
                if ch not in '><' and lastptrdelta != 0:
                    assert lastmemdelta == 0
                    nodestack[-1].append(Node_PtrDelta(lastptrdelta))
                    lastptrdelta = 0

                if ch == '+':
                    lastmemdelta += 1
                elif ch == '-':
                    lastmemdelta -= 1
                elif ch == '>':
                    lastptrdelta += 1
                elif ch == '<':
                    lastptrdelta -= 1
                elif ch == '.':
                    nodestack[-1].append(Node_Output())
                elif ch == ',':
                    nodestack[-1].append(Node_Input())
                elif ch == '[':
                    nodestack.append(Node_LoopWhile())
                elif ch == ']':
                    if len(nodestack) < 2:
                        raise ValueError('Not matching ] at line %d' % (lineno+1))
                    loop = nodestack.pop()
                    nodestack[-1].append(loop)

        if lastmemdelta != 0:
            nodestack[-1].append(Node_MemDelta(lastmemdelta))
        if lastptrdelta != 0:
            nodestack[-1].append(Node_PtrDelta(lastptrdelta))
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')

        return nodestack[0]

def main(argv):
    if len(argv) < 2:
        print >>sys.stderr, 'Usage: %s filename' % argv[0]
        return 1

    parser = Parser()
    node = parser.parse(file(argv[1], 'r'))
    print node
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

