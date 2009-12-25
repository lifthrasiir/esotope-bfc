# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.memstate import *

class TestMemstateOps:
    def test_set_propagate(self):
        m = MemoryState()
        assert m.memory == {}

        ret = m.set(1, Expr[3]+4)
        assert not ret
        assert m.memory == {1: Expr[3]+4}
        ret = m.set(2, Expr[1]*5)
        assert not ret
        assert m.memory == {1: Expr[3]+4, 2: (Expr[3]+4)*5}
        ret = m.set(4, Expr[1]-4)
        assert not ret
        assert m.memory == {1: Expr[3]+4, 2: (Expr[3]+4)*5, 4: Expr[3]}

    def test_set_self(self):
        m = MemoryState()

        ret = m.set(1, Expr[3]+4)
        assert not ret
        ret = m.set(2, Expr[1]*5)
        assert not ret
        ret = m.set(3, Expr[3]-4)
        assert set(ret) == set([SetMemory(3, Expr[3]-4)])
        assert m.memory == {1: Expr[3]+8, 2: (Expr[3]+8)*5}
        ret = m.set(3, Expr[4]-Expr[3]/3*2+5*Expr[6])
        assert set(ret) == set([SetMemory(3, Expr[4]-Expr[3]/3*2+5*Expr[6])])
        assert m.memory == {1: (Expr[4]+5*Expr[6]-Expr[3])/2*3+8,
                            2: ((Expr[4]+5*Expr[6]-Expr[3])/2*3+8)*5}
        ret = m.set(3, Expr[3]%8-2)  # non-invertible assignment
        assert set(ret) == set([SetMemory(1, (Expr[4]+5*Expr[6]-Expr[3])/2*3+8),
                                SetMemory(2, ((Expr[4]+5*Expr[6]-Expr[3])/2*3+8)*5),
                                SetMemory(3, Expr[3]%8-2)])
        assert m.memory == {}

