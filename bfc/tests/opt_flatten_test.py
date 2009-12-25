# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.cond import *
from bfc.nodes import *
from bfc.tests.utils import *

from bfc.opt.flatten import OptimizerPass

transform = OptimizerPass(None).transform

class TestFlattenPass:
    def test_merge(self):
        assert eq(transform(Program([])), 'Program[]')
        assert eq(transform(Program([AdjustMemory(0, 1)])), 'Program[{0}+=1]')
        assert eq(transform(Program([AdjustMemory(0, 1), AdjustMemory(0, 1)])),
                '''Program[{0}+=2]''')
        assert eq(transform(Program([AdjustMemory(0, 1), AdjustMemory(0, -1)])),
                '''Program[]''')
        assert eq(transform(Program([AdjustMemory(0, 1), AdjustMemory(1, 1),
                                     AdjustMemory(0, -1)])),
                '''Program[{1}+=1]''')

    def test_pointer(self):
        assert eq(transform(Program([AdjustMemory(0, 3), MovePointer(7),
                                     AdjustMemory(-7, -3)])),
                '''Program[MovePointer[7]]''')

    def test_pointer_others(self):
        assert eq(transform(Program([MovePointer(42), If(MemNotEqual(0), [Output(42)])])),
                '''Program[If[{42}; Output[42]], MovePointer[42]]''')

