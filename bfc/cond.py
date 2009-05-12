# This is a part of Esotope Brainfuck-to-C Compiler.

from bfc.expr import *

class Condition(object):
    def __nonzero__(self): return True
    def references(self): return set()
    def movepointer(self, offset): return self
    def withmemory(self, map): return self

class Always(Condition):
    def __str__(self): return '1'
    def __repr__(self): return 'True'

class Never(Condition):
    def __nonzero__(self): return False
    def __str__(self): return '0'
    def __repr__(self): return 'False'

class MemNotEqual(Condition):
    def __init__(self, target, value=0):
        self.target = target
        self.value = value

    def references(self):
        return set([self.target])

    def movepointer(self, offset):
        return MemNotEqual(self.target + offset, self.value)

    def withmemory(self, map):
        try:
            if map[self.target] != self.value:
                return Always()
            else:
                return Never()
        except KeyError:
            return self

    def __str__(self):
        if self.value == 0:
            return 'p[%s]' % self.target
        else:
            return 'p[%s] != %s' % (self.target, self.value)

    def __repr__(self):
        if self.value == 0:
            return 'p[%r]' % self.target
        else:
            return 'p[%r]!=%r' % (self.target, self.value)

class ExprNotEqual(Condition):
    def __init__(self, expr, value=0):
        self.expr = Expr(expr)
        self.value = value

    def references(self):
        return self.expr.references()

    def movepointer(self, offset):
        return ExprNotEqual(self.expr.movepointer(offset), self.value)

    def withmemory(self, map):
        expr = self.expr.withmemory(map)
        if expr.simple():
            if int(expr) != self.value:
                return Always()
            else:
                return Never()
        else:
            return ExprNotEqual(expr, self.value)

    def __str__(self):
        return '%s != %s' % (self.expr, self.value)

    def __repr__(self):
        return '%r!=%r' % (self.expr, self.value)

