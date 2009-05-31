# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *

class TestExprOps:
    def test_init_number(self):
        assert Expr().code == 0
        for v in [-9, -4, -1, 0, 1, 4, 9]:
            assert Expr(v).code == v

    def test_init_mem(self):
        for v in [-9, -4, -1, 0, 1, 4, 9]:
            assert Expr[v].code == (Expr.REF, v)

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

