# This is a part of Esotope Brainfuck Compiler.

from cStringIO import StringIO
from bfc.tests.utils import *

from bfc.parser.brainfuck import Parser

parse = Parser(None).parse

class TestBrainfuckParser:
    def test_empty(self):
        assert eq(parse(StringIO('')), 'Program[]')

    def test_adjustmemory(self):
        assert eq(parse(StringIO('+')), 'Program[{0}+=1]')
        assert eq(parse(StringIO('++')), 'Program[{0}+=2]')
        assert eq(parse(StringIO('+++')), 'Program[{0}+=3]')
        assert eq(parse(StringIO('++++')), 'Program[{0}+=4]')
        assert eq(parse(StringIO('-')), 'Program[{0}-=1]')
        assert eq(parse(StringIO('--')), 'Program[{0}-=2]')
        assert eq(parse(StringIO('---')), 'Program[{0}-=3]')
        assert eq(parse(StringIO('----')), 'Program[{0}-=4]')
        assert eq(parse(StringIO('+-')), 'Program[{0}+=1, {0}-=1]')
        assert eq(parse(StringIO('--++')), 'Program[{0}-=2, {0}+=2]')
        assert eq(parse(StringIO('+++---')), 'Program[{0}+=3, {0}-=3]')
        assert eq(parse(StringIO('----++++')), 'Program[{0}-=4, {0}+=4]')

    def test_movepointer(self):
        assert eq(parse(StringIO('>')), 'Program[MovePointer[1]]')
        assert eq(parse(StringIO('>>')), 'Program[MovePointer[2]]')
        assert eq(parse(StringIO('>>>')), 'Program[MovePointer[3]]')
        assert eq(parse(StringIO('>>>>')), 'Program[MovePointer[4]]')
        assert eq(parse(StringIO('<')), 'Program[MovePointer[-1]]')
        assert eq(parse(StringIO('<<')), 'Program[MovePointer[-2]]')
        assert eq(parse(StringIO('<<<')), 'Program[MovePointer[-3]]')
        assert eq(parse(StringIO('<<<<')), 'Program[MovePointer[-4]]')
        assert eq(parse(StringIO('><')), 'Program[MovePointer[1], MovePointer[-1]]')
        assert eq(parse(StringIO('<<>>')), 'Program[MovePointer[-2], MovePointer[2]]')
        assert eq(parse(StringIO('>>><<<')), 'Program[MovePointer[3], MovePointer[-3]]')
        assert eq(parse(StringIO('<<<<>>>>')), 'Program[MovePointer[-4], MovePointer[4]]')

    def test_mix_ops(self):
        assert eq(parse(StringIO('+->><->++++<<>--<+++++')),
                '''Program[{0}+=1, {0}-=1, MovePointer[2], MovePointer[-1],
                           {0}-=1, MovePointer[1], {0}+=4, MovePointer[-2],
                           MovePointer[1], {0}-=2, MovePointer[-1], {0}+=5]''')

    def test_io(self):
        assert eq(parse(StringIO('....,,,,')),
                '''Program[Output[{0}], Output[{0}], Output[{0}], Output[{0}],
                           {0}=Input[], {0}=Input[], {0}=Input[], {0}=Input[]]''')
        assert eq(parse(StringIO('+++.+++')), 'Program[{0}+=3, Output[{0}], {0}+=3]')
        assert eq(parse(StringIO('---.---')), 'Program[{0}-=3, Output[{0}], {0}-=3]')

    def test_loop(self):
        assert eq(parse(StringIO('++[]++')),
                '''Program[{0}+=2, While[{0}; ], {0}+=2]''')
        assert eq(parse(StringIO('--[[]]--')),
                '''Program[{0}-=2, While[{0}; While[{0}; ]], {0}-=2]''')
        assert eq(parse(StringIO('>>[[[]]]>>')),
                '''Program[MovePointer[2], While[{0}; While[{0}; While[{0}; ]]],
                           MovePointer[2]]''')
        assert eq(parse(StringIO('>>[>>++<<]<<')),
                '''Program[MovePointer[2], While[{0}; MovePointer[2], {0}+=2,
                                                      MovePointer[-2]],
                           MovePointer[-2]]''')

    def test_loop_error(self):
        raises(ValueError, '''parse(StringIO('++[--'))''')
        raises(ValueError, '''parse(StringIO('++[--[>>]<<'))''')
        raises(ValueError, '''parse(StringIO('++[--[>>[<<'))''')
        raises(ValueError, '''parse(StringIO('++[--]>>]<<'))''')

    def test_unknown(self):
        assert eq(parse(StringIO('this is\nunknown.')), 'Program[Output[{0}]]')
        assert eq(parse(StringIO('++ ++')), 'Program[{0}+=2, {0}+=2]')

