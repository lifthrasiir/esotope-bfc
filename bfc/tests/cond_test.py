# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.cond import *

class TestExprOps:
    def test_always_never(self):
        always = Always()
        never = Never()
        assert always == Always()
        assert always != never
        assert Never() == never

        assert always.movepointer(42) == always
        assert always.withmemory({0: 42}) == always
        assert never.movepointer(42) == never
        assert never.withmemory({0: 42}) == never

    def test_memnotequal(self):
        m0ne2 = MemNotEqual(0, 2)
        m0ne4 = MemNotEqual(0, 4)
        m1ne4 = MemNotEqual(1, 4)
        assert m0ne2 != m0ne4 != m1ne4
        assert m0ne2 == MemNotEqual(0, 2)
        assert type(m1ne4) is MemNotEqual
        assert m1ne4.target == 1
        assert m1ne4.expr == Expr[1]

        assert m0ne4.movepointer(1) == m1ne4
        assert m1ne4.movepointer(-1) == m0ne4
        assert m0ne4.withmemory({0: 7}) == Always()
        assert m0ne4.withmemory({0: 4}) == Never()
        assert m0ne4.withmemory({0: Expr[3] * 6}) not in (Always(), Never())
            # ^ should not be contracted!

    def test_notequal(self):
        m6p3ne5 = NotEqual(Expr[6] + 3, 5)
        assert type(m6p3ne5) is MemNotEqual
        assert m6p3ne5 == MemNotEqual(6, 2)

        mm7ne5 = MemNotEqual(Expr[7], 5)
        assert type(mm7ne5) is NotEqual
        assert mm7ne5.expr == Expr[Expr[7]]

        assert mm7ne5.movepointer(1) == NotEqual(Expr[Expr[8]+1], 5)
        assert mm7ne5.movepointer(-1) == NotEqual(Expr[Expr[6]-1], 5)
        assert mm7ne5.withmemory({7:9}) == MemNotEqual(9, 5)
        assert type(mm7ne5.withmemory({7:9})) is MemNotEqual

