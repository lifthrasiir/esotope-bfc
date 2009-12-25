# This is a part of Esotope Brainfuck Compiler.

from bfc.tests.utils import *

def test_remove_spaces():
    assert remove_spaces('-Foo[]+Bar()*Baz{}/Quux0123=zzz.') == '-Foo[]+Bar()*Baz{}/Quux0123=zzz.'
    assert remove_spaces('  foo   bar  quux\tz\nq\r+3\t\t ') == 'foobarquuxzq+3'
    assert remove_spaces("Foo['sp       a ces']") == "Foo['sp       a ces']"
    assert remove_spaces('Foo["sp       a ces"]') == 'Foo["sp       a ces"]'

def test_eq():
    return eq([1, 2, 3, 4], '[1,2,3,4]')

