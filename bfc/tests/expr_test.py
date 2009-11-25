# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.tests.utils import *

class TestExprOps:
    def test_init_number(self):
        assert Expr() == 0
        for v in [-9, -4, -1, 0, 1, 4, 9]:
            assert isinstance(Expr(v), LinearExpr)

    def test_init_mem(self):
        for v in [-9, -4, -1, 0, 1, 4, 9]:
            assert isinstance(Expr[v], ReferenceExpr)

    def test_is_simple(self):
        assert Expr().simple()
        for v in [-9, -4, -1, 0, 1, 4, 9]:
            assert Expr(v).simple()
            assert not Expr[v].simple()

    def test_eq_simple(self):
        assert Expr() == Expr(0)
        assert Expr(42) == Expr(42)
        assert Expr(42) == 42
        assert Expr[7] == Expr[7]
        assert Expr(42) != Expr(-42)
        assert Expr(42) != 43
        assert Expr[7] != Expr[8]
        assert Expr[0] != Expr(0)

    def test_ops_simple(self):
        assert (Expr(3) + Expr(4)).simple()
        assert (Expr(3) - Expr(4)).simple()
        assert (Expr(3) * Expr(4)).simple()
        assert (Expr(3) // Expr(4)).simple()
        assert (Expr(3) % Expr(4)).simple()
        for u in xrange(-9, 10):
            assert Expr(u) == u
            for v in xrange(-9, 10):
                assert (Expr(u) + Expr(v)) == (u+v)
                assert (Expr(u) + v) == (u+v)
                assert (u + Expr(v)) == (u+v)
                assert (Expr(u) - Expr(v)) == (u-v)
                assert (Expr(u) - v) == (u-v)
                assert (u - Expr(v)) == (u-v)
                assert (Expr(u) * Expr(v)) == (u*v)
                assert (Expr(u) * v) == (u*v)
                assert (u * Expr(v)) == (u*v)
                if u > 0 and v > 0:
                    assert (Expr(u) // Expr(v)) == (u//v)
                    assert (Expr(u) // v) == (u//v)
                    assert (u // Expr(v)) == (u//v)
                    assert (Expr(u) % Expr(v)) == (u%v)
                    assert (Expr(u) % v) == (u%v)
                    assert (u % Expr(v)) == (u%v)
            if u == 0:
                assert not Expr(u)
            else:
                assert Expr(u)

    def test_add(self):
        assert Expr[4] + 0 == Expr[4]
        assert 0 + Expr[4] == Expr[4]
        assert Expr[4] - 0 == Expr[4]
        assert 0 - Expr[4] == -Expr[4]
        assert Expr[4] + Expr[3] == Expr[3] + Expr[4]
        assert Expr[4] + 3 == 3 + Expr[4]
        assert Expr[4] - Expr[4] == 0
        assert (-Expr[4]) + Expr[4] == 0
        assert (Expr[4] + 7) + 9 == Expr[4] + 16
        assert Expr[4] + 5 and Expr[4] - 5

    def test_mul(self):
        assert Expr[4] * 0 == 0
        assert Expr[4] * 1 == Expr[4]
        assert Expr[4] * -1 == -Expr[4]
        assert Expr[4] * 4 == 4 * Expr[4]
        assert Expr[4] * Expr[3] == Expr[3] * Expr[4]
        assert (Expr[1] * Expr[2]) * (Expr[3] * Expr[4]) == \
                Expr[1] * (Expr[2] * Expr[3]) * Expr[4]
        assert 4 * (Expr[5] * 5) == 20 * Expr[5]
        assert Expr[1] * Expr[2] * Expr[3] * Expr[4]

    def test_add_linear(self):
        assert Expr[3] * 4 + Expr[3] * 5 == Expr[3] * 9
        assert Expr[3] * 4 + (-4) * Expr[3] == 0
        assert (Expr[3] + 7) - Expr[3] == 7
        assert Expr[3] + Expr[3] == 2 * Expr[3]
        assert Expr[3] + Expr[3] - 7 * Expr[3] == -5 * Expr[3]
        assert (Expr[3] * 4 + 5) * 6 - 7 == Expr[3] * 24 + 23

    def test_neg(self):
        assert -Expr(7) == -7
        assert -(-Expr(7)) == 7
        assert -(-(-Expr[7])) == -Expr[7]
        assert -(Expr[3] + Expr[5]) == (-Expr[3]) + (-Expr[5])
        assert -(7 * Expr[3] - 4 * Expr[5]) == 4 * Expr[5] - 7 * Expr[3]
        assert -Expr[3]

    def test_exactdiv(self):
        raises(ValueError, '''Expr(407) / 4''')
        assert Expr(408) / 4 == 102
        raises(ValueError, '''Expr(409) / 4''')
        assert Expr(0) / 4 == 0
        assert Expr[6] / 1 == Expr[6]
        assert Expr[6] / -1 == -Expr[6]
        assert Expr[6] / 2 == (Expr[6] + 3 - 3) / 2
        assert Expr[6] / 5

    def test_div(self):
        assert Expr(407) // 4 == 101
        assert Expr(408) // 4 == 102
        assert Expr(409) // 4 == 102
        assert Expr(0) // 4 == 0
        assert Expr[6] // 1 == Expr[6]
        assert Expr[6] // -1 == -Expr[6]
        assert Expr[6] // 2 == (Expr[6] + 3 - 3) // 2
        assert Expr[6] // 5

    def test_mod(self):
        assert Expr(407) % 4 == 3
        assert Expr(408) % 4 == 0
        assert Expr(409) % 4 == 1
        assert Expr(0) % 4 == 0
        assert Expr[6] % 2 == (Expr[6] + 3 - 3) % 2
        assert Expr[6] % 5

    def test_references(self):
        assert Expr(42).references() == frozenset()
        assert Expr[42].references() == frozenset([42])
        assert Expr[42+Expr[54]].references() == frozenset([54, 42+Expr[54]])
        assert Expr[Expr[1]+Expr[2]].references() == frozenset([1, 2, Expr[1]+Expr[2]])

        assert (-Expr[1]).references() == frozenset([1])
        assert (Expr[1] + Expr[2]).references() == frozenset([1, 2])
        assert (Expr[1] - Expr[2]).references() == frozenset([1, 2])
        assert (Expr[1] * Expr[2]).references() == frozenset([1, 2])
        assert (Expr[1] / Expr[2]).references() == frozenset([1, 2])
        assert (Expr[1] // Expr[2]).references() == frozenset([1, 2])
        assert (Expr[1] % Expr[2]).references() == frozenset([1, 2])

    def test_movepointer(self):
        assert Expr(42).movepointer(5) == Expr(42)
        assert Expr[42].movepointer(5) == Expr[47]
        assert Expr[42+Expr[54]].movepointer(5) == Expr[47+Expr[59]]
        assert Expr[Expr[1]+Expr[2]].movepointer(5) == Expr[5+Expr[6]+Expr[7]]

        assert (-Expr[1]).movepointer(5) == -Expr[6]
        assert (Expr[1] + Expr[2]).movepointer(5) == Expr[6] + Expr[7]
        assert (Expr[1] - Expr[2]).movepointer(5) == Expr[6] - Expr[7]
        assert (Expr[1] * Expr[2]).movepointer(5) == Expr[6] * Expr[7]
        assert (Expr[1] / Expr[2]).movepointer(5) == Expr[6] / Expr[7]
        assert (Expr[1] // Expr[2]).movepointer(5) == Expr[6] // Expr[7]
        assert (Expr[1] % Expr[2]).movepointer(5) == Expr[6] % Expr[7]

    def test_withmemory(self):
        assert Expr(42).withmemory({1:2, 3:4}) == Expr(42)
        assert Expr[42].withmemory({1:2, 3:4}) == Expr[42]
        assert Expr[42].withmemory({42:54}) == 54
        assert Expr[42].withmemory({42:Expr[54], 54:-1}) == -1
        assert Expr[42+Expr[54]].withmemory({54:6}) == Expr[48]
        assert Expr[42+Expr[54]].withmemory({54:6, 48:7}) == 7
        assert Expr[Expr[1]+Expr[2]].withmemory({1:3, 2:-1}) == -1

        assert (-Expr[1]).withmemory({1:8}) == -8
        assert (Expr[1] + Expr[2]).withmemory({1:8, 2:5}) == 13
        assert (Expr[1] + Expr[2]).withmemory({1:0}) == Expr[2]
        assert (Expr[1] + Expr[2]).withmemory({2:0}) == Expr[1]
        assert (Expr[1] - Expr[2]).withmemory({1:8, 2:5}) == 3
        assert (Expr[1] - Expr[2]).withmemory({1:0}) == -Expr[2]
        assert (Expr[1] - Expr[2]).withmemory({2:0}) == Expr[1]
        assert (Expr[1] * Expr[2]).withmemory({1:8, 2:5}) == 40
        assert (Expr[1] * Expr[2]).withmemory({1:0}) == 0
        assert (Expr[1] * Expr[2]).withmemory({1:1}) == Expr[2]
        assert (Expr[1] * Expr[2]).withmemory({1:-1}) == -Expr[2]
        assert (Expr[1] * Expr[2]).withmemory({2:0}) == 0
        assert (Expr[1] * Expr[2]).withmemory({2:1}) == Expr[1]
        assert (Expr[1] * Expr[2]).withmemory({2:-1}) == -Expr[1]
        raises(ValueError, '''(Expr[1] / Expr[2]).withmemory({1:8, 2:5})''')
        assert (Expr[1] / Expr[2]).withmemory({2:1}) == Expr[1]
        assert (Expr[1] / Expr[2]).withmemory({2:-1}) == -Expr[1]
        assert (Expr[1] / Expr[2]).withmemory({1:8, 2:4}) == 2
        assert (Expr[1] // Expr[2]).withmemory({1:8, 2:5}) == 1
        assert (Expr[1] // Expr[2]).withmemory({2:1}) == Expr[1]
        assert (Expr[1] // Expr[2]).withmemory({2:-1}) == -Expr[1]
        assert (Expr[1] % Expr[2]).withmemory({1:8, 2:5}) == 3

