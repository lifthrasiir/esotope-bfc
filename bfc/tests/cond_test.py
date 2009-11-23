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
        assert always and not never

        assert always.references() == frozenset()
        assert always.movepointer(42) == always
        assert always.withmemory({0: 42}) == always
        assert never.references() == frozenset()
        assert never.movepointer(42) == never
        assert never.withmemory({0: 42}) == never

    def test_memequality(self):
        m0e2 = MemEqual(0, 2); m0ne2 = MemNotEqual(0, 2)
        m0e4 = MemEqual(0, 4); m0ne4 = MemNotEqual(0, 4)
        m1e4 = MemEqual(1, 4); m1ne4 = MemNotEqual(1, 4)
        assert m0e2 and m0ne2 and m0e4 and m0ne4 and m1e4 and m1ne4
        assert m0e2 != m0e4 != m1e4 != m1ne4 != m0ne4 != m0ne2
        assert ~m0e2 == m0ne2 and ~m0e4 == m0ne4 and ~m1e4 == m1ne4
        assert m0e2 == ~m0ne2 and m0e4 == ~m0ne4 and m1e4 == ~m1ne4
        assert m0e2 == MemEqual(0, 2) and m0ne2 == MemNotEqual(0, 2)
        assert type(m1e4) is MemEqual and type(m1ne4) is MemNotEqual
        assert m1e4.target == m1ne4.target == 1
        assert m1e4.expr == m1ne4.expr == Expr[1]

        assert m0e4.references() == m0ne4.references() == frozenset([0])
        assert m0e4.movepointer(1) == m1e4 and m0ne4.movepointer(1) == m1ne4
        assert m1e4.references() == m1ne4.references() == frozenset([1])
        assert m1e4.movepointer(-1) == m0e4 and m1ne4.movepointer(-1) == m0ne4
        assert m0e4.withmemory({0: 4}) == m0ne4.withmemory({0: 7}) == Always()
        assert m0e4.withmemory({0: 7}) == m0ne4.withmemory({0: 4}) == Never()
        assert m0e4.withmemory({0: Expr[3] * Expr[4]}) not in (Always(), Never())
        assert m0ne4.withmemory({0: Expr[3] * Expr[4]}) not in (Always(), Never())

    def test_equality(self):
        assert NotEqual(5, 6) == Equal(6, 6) == Always()
        assert NotEqual(6, 6) == Equal(5, 6) == Never()
        assert NotEqual(Expr[1] * 4 + 3, -13) == NotEqual(Expr[1] * 4, -16) \
                                              == NotEqual(Expr[1], -4)
        assert Equal(Expr[1] * 4 + 3, -13) == Equal(Expr[1] * 4, -16) \
                                           == Equal(Expr[1], -4)
        assert ~NotEqual(Expr[1] * 4 + 3, -13) == Equal(Expr[1] * 4 + 3, -13)
        assert NotEqual(Expr[1] * 4 + 3, -13) == ~Equal(Expr[1] * 4 + 3, -13)
        assert NotEqual(Expr[1] * 4 + 3, 5) == NotEqual(Expr[1] * 4, 2) == Always()
        assert Equal(Expr[1] * 4 + 3, 5) == Equal(Expr[1] * 4, 2) == Never()
        assert NotEqual(Expr[1] / 8, 6) == NotEqual(Expr[1], 48)
        assert NotEqual(Expr[1] / 8, 0) == NotEqual(Expr[1], 0)
        assert Equal(Expr[1] / 8, 6) == Equal(Expr[1], 48)
        assert Equal(Expr[1] / 8, 0) == Equal(Expr[1], 0)

        m6p3e5 = Equal(Expr[6] + 3, 5); m6p3ne5 = NotEqual(Expr[6] + 3, 5)
        assert type(m6p3e5) is MemEqual and type(m6p3ne5) is MemNotEqual
        assert m6p3e5 == MemEqual(6, 2) and m6p3ne5 == MemNotEqual(6, 2)

        mm7e5 = MemEqual(Expr[7], 5); mm7ne5 = MemNotEqual(Expr[7], 5)
        assert type(mm7e5) is Equal and type(mm7ne5) is NotEqual
        assert mm7e5.expr == mm7ne5.expr == Expr[Expr[7]]

        assert mm7e5.references() == mm7ne5.references() == frozenset([Expr[7]])
        assert mm7e5.movepointer(1) == Equal(Expr[Expr[8]+1], 5)
        assert mm7ne5.movepointer(1) == NotEqual(Expr[Expr[8]+1], 5)
        assert mm7e5.movepointer(-1) == Equal(Expr[Expr[6]-1], 5)
        assert mm7ne5.movepointer(-1) == NotEqual(Expr[Expr[6]-1], 5)
        assert mm7e5.withmemory({7:9}) == MemEqual(9, 5)
        assert mm7ne5.withmemory({7:9}) == MemNotEqual(9, 5)
        assert type(mm7e5.withmemory({7:9})) is MemEqual
        assert type(mm7ne5.withmemory({7:9})) is MemNotEqual

