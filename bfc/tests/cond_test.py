# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.cond import *

class TestCondOps:
    def test_always_never(self):
        always = Always()
        never = Never()
        assert always and not never
        assert always == Always()
        assert always != never
        assert Never() == never
        assert ~always == never and always == ~never

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

        assert mm7e5.references() == mm7ne5.references() == frozenset([7, Expr[7]])
        assert mm7e5.movepointer(1) == Equal(Expr[Expr[8]+1], 5)
        assert mm7ne5.movepointer(1) == NotEqual(Expr[Expr[8]+1], 5)
        assert mm7e5.movepointer(-1) == Equal(Expr[Expr[6]-1], 5)
        assert mm7ne5.movepointer(-1) == NotEqual(Expr[Expr[6]-1], 5)
        assert mm7e5.withmemory({7:9}) == MemEqual(9, 5)
        assert mm7ne5.withmemory({7:9}) == MemNotEqual(9, 5)
        assert type(mm7e5.withmemory({7:9})) is MemEqual
        assert type(mm7ne5.withmemory({7:9})) is MemNotEqual

    def test_range(self):
        assert Range(Expr[5]) == Never()
        assert Range(Expr[5], 15) == MemEqual(5, 15)
        assert Range(Expr[5], (None,14), (16,None)) == MemNotEqual(5, 15)
        assert Range(Expr[5], (None,10), (5,None)) == Always()

        m3pm4 = Expr[3+Expr[4]];             m6pm7 = Expr[6+Expr[7]]
        m3pm4lt5 = Less(m3pm4, 5);           m6pm7lt5 = Less(m6pm7, 5)
        m3pm4le5 = LessOrEqual(m3pm4, 5);    m6pm7le5 = LessOrEqual(m6pm7, 5)
        m3pm4e5 = Equal(m3pm4, 5);           m6pm7e5 = Equal(m6pm7, 5)
        m3pm4ge5 = GreaterOrEqual(m3pm4, 5); m6pm7ge5 = GreaterOrEqual(m6pm7, 5)
        m3pm4gt5 = Greater(m3pm4, 5);        m6pm7gt5 = Greater(m6pm7, 5)

        assert m3pm4lt5 and m3pm4le5 and m3pm4e5 and m3pm4ge5 and m3pm4gt5
        assert m3pm4lt5 == LessOrEqual(m3pm4, 4) and m3pm4gt5 == GreaterOrEqual(m3pm4, 6)
        assert m3pm4lt5 == ~m3pm4ge5 and ~m3pm4lt5 == m3pm4ge5
        assert m3pm4le5 == ~m3pm4gt5 and ~m3pm4le5 == m3pm4gt5
        assert (m3pm4lt5.references() == m3pm4le5.references() == m3pm4e5.references() ==
                m3pm4ge5.references() == m3pm4gt5.references() == m3pm4.references())
        assert m3pm4lt5.movepointer(3) == m6pm7lt5
        assert m3pm4le5.movepointer(3) == m6pm7le5
        assert m3pm4ge5.movepointer(3) == m6pm7ge5
        assert m3pm4gt5.movepointer(3) == m6pm7gt5
        assert m3pm4lt5.withmemory({4: 5, 8: 15, 15: 23}) == Never()
        assert m3pm4le5.withmemory({4: 5, 8: 15, 15: 23}) == Never()
        assert m3pm4ge5.withmemory({4: 5, 8: 15, 15: 23}) == Always()
        assert m3pm4gt5.withmemory({4: 5, 8: 15, 15: 23}) == Always()

        m7e13579 = Range(Expr[7], 1, 3, 5, 7, 9)
        assert m7e13579
        assert m7e13579.expr == Expr[7]
        assert m7e13579.ranges == ((1,1), (3,3), (5,5), (7,7), (9,9))
        assert ~m7e13579 == Range(Expr[7], (None,0), 2, 4, 6, 8, (10,None))
        assert m7e13579 == Range(Expr[7]+1, 2, 4, 6, 8, 10)
        assert m7e13579 == Range(Expr[7]*2+3, 9, 5, 13, 21, 17)
        assert m7e13579 == Range(-Expr[7]*2+3, 1, -3, -7, -11, -15)
        assert m7e13579 == Range((Expr[7]-1)/2*7, 0, 7, 14, 21, 28)

    def test_conjunction(self):
        assert (Always() & Always()) == Always()
        assert ((Always() & Never()) == (Never() & Always()) ==
                (Never() & Never()) == Never())

        m1lt5 = Less(Expr[1], 5); m1le5 = LessOrEqual(Expr[1], 5)
        m1e5 = Equal(Expr[1], 5); m1ne5 = NotEqual(Expr[1], 5)
        m1ge5 = GreaterOrEqual(Expr[1], 5); m1gt5 = Greater(Expr[1], 5)
        assert (m1lt5 & m1le5) == (m1ne5 & m1le5) == m1lt5
        assert (m1gt5 & m1ge5) == (m1ne5 & m1ge5) == m1gt5
        assert (m1le5 & m1ge5) == m1e5
        assert (m1lt5 & m1ge5) == (m1gt5 & m1le5) == (m1lt5 & m1gt5) == Never()
        assert (m1e5 & m1ne5) == Never()

        assert ((Range(Expr[3], (None,-5), (0,4), (7,9), (13,25), (48,None)) &
                 Range(Expr[3], (None,1), (6,12), 21, (37,49), (53,68), (70,None))) ==
                Range(Expr[3], (None,-5), (0,1), (7,9), 21, (48,49), (53,68), (70,None)))

        m3e5andm4ne7 = MemEqual(3, 5) & MemNotEqual(4, 7)
        assert ~m3e5andm4ne7 == (MemNotEqual(3, 5) | MemEqual(4, 7))
        assert m3e5andm4ne7.references() == frozenset([3, 4])
        assert m3e5andm4ne7.movepointer(-1) == (MemNotEqual(3, 7) & MemEqual(2, 5))
        assert m3e5andm4ne7.withmemory({3: 5}) == MemNotEqual(4, 7)
        assert m3e5andm4ne7.withmemory({3: 5, 4: 6}) == Always()
        assert m3e5andm4ne7.withmemory({3: 8}) == Never()

    def test_disjunction(self):
        assert ((Always() | Always()) == (Always() | Never()) ==
                (Never() | Always()) == Always())
        assert (Never() | Never()) == Never()

        m1lt5 = Less(Expr[1], 5); m1le5 = LessOrEqual(Expr[1], 5)
        m1e5 = Equal(Expr[1], 5); m1ne5 = NotEqual(Expr[1], 5)
        m1ge5 = GreaterOrEqual(Expr[1], 5); m1gt5 = Greater(Expr[1], 5)
        assert (m1lt5 | m1le5) == (m1lt5 | m1e5) == m1le5
        assert (m1gt5 | m1ge5) == (m1gt5 | m1e5) == m1ge5
        assert (m1lt5 | m1gt5) == m1ne5
        assert (m1le5 | m1ge5) == (m1lt5 | m1e5 | m1gt5) == Always()
        assert (m1e5 | m1ne5) == Always()
        assert (m1e5 | Equal(Expr[1], 11)) == Range(Expr[1], 5, 11)
        assert type(m1e5 | Equal(Expr[2], 5)) is Disjunction

        assert ((Range(Expr[3], (None,-5), (0,4), (7,9), (13,25), (48,None)) |
                 Range(Expr[3], (None,1), (6,12), 21, (37,49), (53,68), (70,None))) ==
                Range(Expr[3], (None,4), (6,25), (37,None)))

        m3e5orm4ne7 = MemEqual(3, 5) | MemNotEqual(4, 7)
        assert ~m3e5orm4ne7 == (MemNotEqual(3, 5) & MemEqual(4, 7))
        assert m3e5orm4ne7.references() == frozenset([3, 4])
        assert m3e5orm4ne7.movepointer(-1) == (MemNotEqual(3, 7) | MemEqual(2, 5))
        assert m3e5orm4ne7.withmemory({3: 5}) == Always()
        assert m3e5orm4ne7.withmemory({3: 8}) == MemNotEqual(4, 7)
        assert m3e5orm4ne7.withmemory({3: 8, 4: 7}) == Never()

    def test_compactrepr(self):
        assert Always().compactrepr() == 'True'
        assert Never().compactrepr() == 'False'

        assert MemEqual(-1, 7).compactrepr() == '{-1}==7'
        assert MemNotEqual(-1, 7).compactrepr() == '{-1}!=7'
        assert Equal(Expr[3+Expr[4]], 7).compactrepr() in ('{3+{4}}==7', '{{4}+3}==7')
        assert Equal(Expr[3+Expr[4]], 0).compactrepr() in ('!{3+{4}}', '!{{4}+3}')
        assert Equal(Expr[3]+Expr[4], 0).compactrepr() in ('!({3}+{4})', '!({4}+{3})')
        assert NotEqual(Expr[3+Expr[4]], 7).compactrepr() in ('{3+{4}}!=7', '{{4}+3}!=7')
        assert NotEqual(Expr[3+Expr[4]], 0).compactrepr() in ('{3+{4}}', '{{4}+3}')
        assert NotEqual(Expr[3]+Expr[4], 0).compactrepr() in ('{3}+{4}', '{4}+{3}')
        assert Range(Expr[5], 1, 3, 5, 7, 9).compactrepr() == '{5}~(1,3,5,7,9)'
        assert (~Range(Expr[5], 1, 3, 5, 7, 9)).compactrepr() == '{5}~(..0,2,4,6,8,10..)'
        assert Range(Expr[5], (1,12), (16,30)).compactrepr() == '{5}~(1..12,16..30)'
        assert Range(Expr[5], (None,8)).compactrepr() == '{5}<=8'
        assert Range(Expr[5], (4,8)).compactrepr() == '4<={5}<=8'
        assert Range(Expr[5], (4,None)).compactrepr() == '4<={5}'

        assert ((MemEqual(1,2) | MemEqual(2,3) | MemEqual(3,4)).compactrepr() in
                ('{1}==2 || {2}==3 || {3}==4', '{1}==2 || {3}==4 || {2}==3',
                 '{2}==3 || {1}==2 || {3}==4', '{2}==3 || {3}==4 || {1}==2',
                 '{3}==4 || {1}==2 || {2}==3', '{3}==4 || {2}==3 || {1}==2'))
        assert ((MemEqual(1,2) & MemEqual(2,3) & MemEqual(3,4)).compactrepr() in
                ('{1}==2 && {2}==3 && {3}==4', '{1}==2 && {3}==4 && {2}==3',
                 '{2}==3 && {1}==2 && {3}==4', '{2}==3 && {3}==4 && {1}==2',
                 '{3}==4 && {1}==2 && {2}==3', '{3}==4 && {2}==3 && {1}==2'))
        assert (((MemEqual(1,2) | MemEqual(2,3)) & MemEqual(3,4)).compactrepr() in
                ('({1}==2 || {2}==3) && {3}==4', '({2}==3 || {1}==2) && {3}==4',
                 '{3}==4 && ({1}==2 || {2}==3)', '{3}==4 && ({2}==3 || {1}==2)'))
        assert (((MemEqual(1,2) & MemEqual(2,3)) | MemEqual(3,4)).compactrepr() in
                ('({1}==2 && {2}==3) || {3}==4', '({2}==3 && {1}==2) || {3}==4',
                 '{3}==4 || ({1}==2 && {2}==3)', '{3}==4 || ({2}==3 && {1}==2)'))

