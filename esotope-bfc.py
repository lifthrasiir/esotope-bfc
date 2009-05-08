#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
import getopt

try: import psyco; psyco.full()
except ImportError: pass


def _setmovepointer(cells, offset):
    result = [i + offset for i in cells if i is not None]
    if None in cells: result.append(None)
    return set(result)

def _formatadjust(ref, value):
    if isinstance(value, (int, long)) or value.simple():
        value = int(value)
        if value == 0:
            return ''
        elif value == 1:
            return '++%s' % ref
        elif value == -1:
            return '--%s' % ref

    s = str(value)
    if s.startswith('-'):
        return '%s -= %s' % (ref, s[1:])
    else:
        return '%s += %s' % (ref, s)

_reprmap = [('\\%03o', '%c')[32 <= i < 127] % i for i in xrange(256)]
_reprmap[0] = '\\0'; _reprmap[9] = '\\t'; _reprmap[10] = '\\n'; _reprmap[13] = '\\r'
_reprmap[34] = '\\"'; _reprmap[39] = '\''; _reprmap[92] = '\\\\'
def _addslashes(s):
    return ''.join(_reprmap[ord(i)] for i in s)

def _gcdex(x, y):
    a = 0; b = 1
    c = 1; d = 0
    while x:
        q = y / x; r = y % x
        u = a - c * q; v = b - d * q
        y = x; x = r
        a = c; b = d
        c = u; d = v
    return (a, b, y)


_EXPRNEG = '_'
_EXPRREF = '@'
_EXPRADD = '+'
_EXPRMUL = '*'
_EXPRDIV = '/'
_EXPRMOD = '%'
_EXPRARITYMAP = {_EXPRNEG: 1, _EXPRREF: 1, _EXPRADD: 2, _EXPRMUL: 2,
                 _EXPRDIV: 2, _EXPRMOD: 2}

class _ExprMeta(type):
    def __getitem__(self, offset):
        return Expr(Expr(offset).code + [_EXPRREF])

class Expr(object):
    __metaclass__ = _ExprMeta
    __slots__ = ['code']

    def __init__(self, obj=0):
        if isinstance(obj, (int, long)):
            self.code = [obj]
        else:
            if isinstance(obj, Expr): obj = obj.code
            self.code = obj[:]

    def __nonzero__(self):
        return (self != 0)

    def __neg__(self):
        code = self.code
        if len(code) == 1: return Expr(-code[0])
        if code[-1] is _EXPRNEG: return Expr(code[:-1])
        return Expr(code + [_EXPRNEG])

    def __pos__(self):
        return self

    def __add__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] + rhscode[0])
            elif lhscode[0] == 0: return rhs
        elif len(rhscode) == 1:
            if rhscode[0] == 0: return lhs
        return Expr(lhscode + rhscode + [_EXPRADD])

    def __radd__(rhs, lhs):
        return Expr(lhs) + rhs

    def __sub__(lhs, rhs):
        return lhs + (-rhs)

    def __rsub__(rhs, lhs):
        return lhs + (-rhs)

    def __mul__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] * rhscode[0])
            elif lhscode[0] == 0: return Expr()
            elif lhscode[0] == 1: return rhs
            elif lhscode[0] == -1: return -rhs
        elif len(rhscode) == 1:
            if rhscode[0] == 0: return Expr()
            elif rhscode[0] == 1: return lhs
            elif rhscode[0] == -1: return -lhs
        return Expr(lhscode + rhscode + [_EXPRMUL])

    def __rmul__(rhs, lhs):
        return Expr(lhs) * rhs

    def __div__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1:
            if len(rhscode) == 1: return Expr(lhscode[0] / rhscode[0])
            elif lhscode[0] == 0: return Expr()
        elif len(rhscode) == 1:
            if rhscode[0] == 1: return lhs
            elif rhscode[0] == -1: return -lhs
        return Expr(lhscode + rhscode + [_EXPRDIV])

    def __rdiv__(rhs, lhs):
        return Expr(lhs) / rhs

    __truediv__ = __div__
    __rtruediv__ = __rdiv__
    __floordiv__ = __div__
    __rfloordiv__ = __rdiv__

    def __mod__(lhs, rhs):
        lhscode = lhs.code
        rhscode = Expr(rhs).code
        if len(lhscode) == 1 and len(rhscode) == 1:
            return Expr(lhscode[0] % rhscode[0])
        return Expr(lhscode + rhscode + [_EXPRMOD])

    def __rmod__(rhs, lhs):
        return Expr(lhs) % rhs

    def __eq__(self, rhs):
        return self.code == Expr(rhs).code

    def __ne__(self, rhs):
        return self.code != Expr(rhs).code

    def __lt__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue < rhsvalue
        except: return False

    def __le__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue <= rhsvalue
        except: return False

    def __gt__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue > rhsvalue
        except: return False

    def __ge__(lhs, rhs):
        try:
            lhsvalue, = lhs.code; rhsvalue, = Expr(rhs).code
            return lhsvalue >= rhsvalue
        except: return False

    def __hash__(self):
        if self.simple():
            return hash(self.code[0])
        return hash(tuple(self.code))

    def __int__(self):
        assert self.simple()
        return self.code[0]

    def _simplify(self, code):
        stack = []

        for c in code:
            if c is _EXPRNEG:
                arg = stack.pop()
                if len(arg) == 1: result = [-arg[0]]
                elif arg[-1] is _EXPRNEG: result = arg[:-1]
                else: result = arg + [_EXPRNEG]

            elif c is _EXPRREF:
                arg = stack.pop()
                result = arg + [_EXPRREF]

            elif c is _EXPRADD:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRADD]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] + rhs[0]]
                    elif lhs[0] == 0: result = rhs
                elif len(rhs) == 1:
                    if rhs[0] == 0: result = lhs

            elif c is _EXPRMUL:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRMUL]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] * rhs[0]]
                    elif lhs[0] == 0: result = [0]
                    elif lhs[0] == 1: result = rhs
                    elif lhs[0] == -1: result = rhs + [_EXPRNEG]
                elif len(rhs) == 1:
                    if rhs[0] == 0: result = [0]
                    elif rhs[0] == 1: result = lhs
                    elif rhs[0] == -1: result = lhs + [_EXPRNEG]

            elif c is _EXPRDIV:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRDIV]
                if len(lhs) == 1:
                    if len(rhs) == 1: result = [lhs[0] / rhs[0]]
                    elif lhs[0] == 0: result = []
                elif len(rhs) == 1:
                    if rhs[0] == 1: result = lhs
                    elif rhs[0] == -1: result = lhs + [_EXPRNEG]

            elif c is _EXPRMOD:
                rhs = stack.pop()
                lhs = stack.pop()
                result = lhs + rhs + [_EXPRMOD]
                if len(lhs) == 1 and len(rhs) == 1:
                    result = [lhs[0] % rhs[0]]

            else:
                result = [c]

            stack.append(result)

        return stack[-1]

    def _getpartial(self, code, i):
        arityneeded = []
        while True:
            arityneeded.append(_EXPRARITYMAP.get(code[i], 0))
            while arityneeded[-1] == 0:
                del arityneeded[-1]
                if not arityneeded: return i
                arityneeded[-1] -= 1
            i -= 1

    def simple(self):
        return len(self.code) == 1

    def simplify(self):
        return Expr(self._simplify(self.code))

    def references(self):
        code = self.code
        getpartial = self._getpartial

        refs = set()
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                refs.add(Expr(code[getpartial(code, i-1):i]))
        return refs

    def movepointer(self, delta):
        code = self.code
        getpartial = self._getpartial
        simplify = self._simplify

        newcode = []
        lastref = 0
        i = 0
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                assert isinstance(code[i-1], (int, long)) # XXX
                newcode.extend(code[lastref:i-1])
                newcode.append(code[i-1] + delta)
                lastref = i # this contains _EXPRREF, which is copied later
        newcode.extend(code[lastref:])
        return Expr(newcode)

    def withmemory(self, map):
        code = self.code
        getpartial = self._getpartial

        newcode = []
        lastref = 0
        i = 0
        for i in xrange(len(code)):
            if code[i] is _EXPRREF:
                assert isinstance(code[i-1], (int, long)) # XXX
                newcode.extend(code[lastref:i-1])
                try:
                    newcode.extend(Expr(map[code[i-1]]).code)
                except KeyError:
                    newcode.extend(code[i-1:i+1])
                lastref = i + 1
        newcode.extend(code[lastref:])
        return Expr(self._simplify(newcode))

    def __str__(self):
        self.code = self._simplify(self.code)
        return repr(self)

    def __repr__(self):
        stack = []
        for c in self.code:
            if c is _EXPRNEG:
                arg = stack.pop()
                stack.append('-%s' % arg)
            elif c is _EXPRREF:
                arg = stack.pop()
                stack.append('p[%s]' % arg)
            elif c is _EXPRADD:
                rhs = stack.pop(); lhs = stack.pop()
                if rhs.startswith('-'):
                    stack.append('(%s%s)' % (lhs, rhs))
                else:
                    stack.append('(%s+%s)' % (lhs, rhs))
            elif c is _EXPRMUL:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s*%s)' % (lhs, rhs))
            elif c is _EXPRDIV:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s/%s)' % (lhs, rhs))
            elif c is _EXPRMOD:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s%%%s)' % (lhs, rhs))
            else:
                stack.append(str(c))
        return stack[-1]


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


class Node(object):
    # returns False if it is a no-op. cleanup pass will remove such no-ops.
    def __nonzero__(self): return True

    # returns False if it does an input or output, thus cannot be reordered.
    def pure(self): return True

    # moves all memory references in it by offset.
    def movepointer(self, offset): raise RuntimeError('not implemented')

    # propagates known memory cells given.
    def withmemory(self, map): pass

    # a set of offset to memory cells which may be referenced/updated by
    # this node, relative to initial pointer before execution.
    # if there are more cells unspecified the cell may include None as well.
    # these methods are used for forward analysis.
    def prereferences(self): return set()
    def preupdates(self): return set()

    # amount of pointer moves. it differs with amount of pointer moves
    # in the loop body only -- use ComplexNode.stride() for it.
    # it may return None if uncertain.
    def offsets(self): return 0

    # similar to pre* methods, but the offsets are relative to final pointer
    # after execution. these methods are used for backward analysis.
    # note that these will be same to pre* ones if offsets() returns 0.
    def postreferences(self): return set()
    def postupdates(self): return set()

    # returns False if this node is an infinite loop.
    def returns(self): return True

class ComplexNode(Node, list):
    def empty(self):
        return len(self) > 0

    def movepointer(self, offset):
        if offset != 0:
            for child in self: child.movepointer(offset)

    def pure(self):
        return all(child.pure() for child in self)

    def stride(self):
        stride = 0
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None: return None
            stride += ioffsets
        return stride

    def bodyprereferences(self):
        offsets = 0
        refs = []
        for child in self:
            refs.extend(_setmovepointer(child.prereferences(), offsets))
            ioffsets = child.offsets()
            if ioffsets is None:
                refs.append(None)
                break
            offsets += ioffsets
        return set(refs)

    def bodypreupdates(self):
        offsets = 0
        updates = []
        for child in self:
            updates.extend(_setmovepointer(child.preupdates(), offsets))
            ioffsets = child.offsets()
            if ioffsets is None:
                updates.append(None)
                break
            offsets += ioffsets
        return set(updates)

    def bodypostreferences(self):
        offsets = 0
        refs = []
        for child in self[::-1]:
            ioffsets = child.offsets()
            if ioffsets is None:
                refs.append(None)
                break
            offsets -= ioffsets
            refs.extend(_setmovepointer(child.postreferences(), offsets))
        return set(refs)

    def bodypostupdates(self):
        offsets = 0
        updates = []
        for child in self[::-1]:
            ioffsets = child.offsets()
            if ioffsets is None:
                updates.append(None)
                break
            offsets -= ioffsets
            updates.extend(_setmovepointer(child.postupdates(), offsets))
        return set(updates)

    def __repr__(self):
        return list.__repr__(self)

class Program(ComplexNode):
    def emit(self, emitter):
        emitter.write('/* generated by esotope-bfc */')
        emitter.write('#include <stdio.h>')
        emitter.write('#include <stdint.h>')
        emitter.write('static uint%d_t m[30000], *p = m;' % emitter.cellsize)
        emitter.write('int main(void) {')
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.write('return 0;')
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'Program[%s]' % ComplexNode.__repr__(self)[1:-1]

class Nop(Node):
    def __nonzero__(self):
        return False

    def emit(self, emitter):
        pass

    def __repr__(self):
        return 'Nop[]'

class SetMemory(Node):
    def __init__(self, offset, value):
        self.offset = offset
        self.value = Expr(value)

    def movepointer(self, offset):
        self.offset += offset
        self.value = self.value.movepointer(offset)

    def withmemory(self, map):
        self.value = self.value.withmemory(map)

    def prereferences(self):
        return self.value.references()
    postreferences = prereferences

    def preupdates(self):
        return set([self.offset])
    postupdates = preupdates

    def emit(self, emitter):
        emitter.write('p[%d] = %s;' % (self.offset, self.value))

    def __repr__(self):
        return '%d=%r' % (self.offset, self.value)

class AdjustMemory(Node):
    def __init__(self, offset, delta):
        self.offset = offset
        self.delta = Expr(delta)

    def __nonzero__(self):
        return self.delta != 0

    def movepointer(self, offset):
        self.offset += offset
        self.delta = self.delta.movepointer(offset)

    def withmemory(self, map):
        self.delta = self.delta.withmemory(map)

    def prereferences(self):
        return set([self.offset]) | self.delta.references()
    postreferences = prereferences

    def preupdates(self):
        return set([self.offset])
    postupdates = preupdates

    def emit(self, emitter):
        stmt = _formatadjust('p[%s]' % self.offset, self.delta)
        if stmt: emitter.write(stmt + ';')

    def __repr__(self):
        if self.delta < 0:
            return '%d-=%r' % (self.offset, -self.delta)
        else:
            return '%d+=%r' % (self.offset, self.delta)

class MovePointer(Node):
    def __init__(self, offset):
        self.offset = offset

    def __nonzero__(self):
        return self.offset != 0

    def movepointer(self, offset):
        pass # no change

    def offsets(self):
        return self.offset

    def emit(self, emitter):
        stmt = _formatadjust('p', self.offset)
        if stmt: emitter.write(stmt + ';')

    def __repr__(self):
        return '@%r' % self.offset

class Input(Node):
    def __init__(self, offset):
        self.offset = offset

    def pure(self):
        return False

    def movepointer(self, offset):
        self.offset += offset

    def preupdates(self):
        return set([self.offset])
    postupdates = preupdates

    def emit(self, emitter):
        emitter.write('p[%s] = getchar();' % self.offset)

    def __repr__(self):
        return 'Input[%r]' % self.offset

class Output(Node):
    def __init__(self, expr):
        self.expr = expr

    def pure(self):
        return False

    def withmemory(self, map):
        self.expr = self.expr.withmemory(map)

    def prereferences(self):
        return self.expr.references()
    postreferences = prereferences

    def movepointer(self, offset):
        self.expr = self.expr.movepointer(offset)

    def emit(self, emitter):
        emitter.write('putchar(%s);' % self.expr)

    def __repr__(self):
        return 'Output[%r]' % self.expr

class OutputConst(Node):
    def __init__(self, s):
        if isinstance(s, str):
            self.str = s
        else:
            self.str = ''.join(chr(i & 0xff) for i in s)

    def __nonzero__(self):
        return len(self.str) > 0

    def pure(self):
        return False

    def movepointer(self, offset):
        pass # does nothing

    def emit(self, emitter):
        for line in self.str.splitlines(True):
            emitter.write('fwrite("%s", 1, %d, stdout);' % (_addslashes(line), len(line)))

    def __repr__(self):
        return 'OutputConst[%r]' % self.str

class SeekMemory(Node):
    def __init__(self, target, stride, value=0):
        self.target = target
        self.stride = stride
        self.value = value

    def offsets(self):
        return None

    def movepointer(self, offset):
        self.target += offset

    def prereferences(self):
        return set([self.target, None])

    def postreferences(self):
        return set([self.target, None])

    def emit(self, emitter):
        accumstmt = _formatadjust('p', self.stride)
        emitter.write('while (p[%d] != %s) %s;' % (self.target, self.value, accumstmt))

    def __repr__(self):
        if self.target == 0:
            return 'SeekMemory[p[%r*k]!=%r]' % (self.stride, self.value)
        else:
            return 'SeekMemory[p[%d+%r*k]!=%r] @%d' % \
                    (self.target, self.stride, self.value, self.target)

class If(ComplexNode):
    def __init__(self, cond=None, children=[]):
        ComplexNode.__init__(self, children)
        if cond is None:
            self.cond = MemNotEqual(0, 0)
        else:
            self.cond = cond

    def __nonzero__(self):
        return bool(self.cond) and len(self) > 0

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.cond = self.cond.movepointer(offset)

    def withmemory(self, map):
        self.cond = self.cond.withmemory(map)

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        return self.bodyprereferences() | self.cond.references()

    def postreferences(self):
        bodyrefs = self.bodypostreferences()
        stride = self.stride()
        if stride is not None:
            bodyrefs.update(_setmovepointer(self.cond.references(), -stride))
        else:
            bodyrefs.add(None) # we don't know where it is.
        return bodyrefs

    def preupdates(self):
        return self.bodypreupdates()

    def postupdates(self):
        return self.bodypostupdates()

    def emit(self, emitter):
        if emitter.debugging:
            emitter.dumpcomplex(self)

        emitter.write('if (%s) {' % self.cond)
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'If[%r; %s]' % (self.cond, ComplexNode.__repr__(self)[1:-1])

class Repeat(ComplexNode):
    def __init__(self, count, children=[]):
        ComplexNode.__init__(self, children)
        self.count = Expr(count)

    def __nonzero__(self):
        return bool(self.count) and len(self) > 0

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.count = self.count.movepointer(offset)

    def withmemory(self, map):
        self.count = self.count.withmemory(map)

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        bodyrefs = self.bodyprereferences()
        stride = self.stride()
        if bodyrefs and stride != 0:
            bodyrefs.add(None)
        return bodyrefs

    def postreferences(self):
        bodyrefs = self.bodypostreferences()
        stride = self.stride()
        if bodyrefs and stride != 0:
            bodyrefs.add(None)
        return bodyrefs

    def preupdates(self):
        bodyupdates = self.bodypreupdates()
        stride = self.stride()
        if bodyupdates and stride != 0:
            bodyupdates.add(None)
        return bodyupdates

    def postupdates(self):
        bodyupdates = self.bodypostupdates()
        stride = self.stride()
        if bodyupdates and stride != 0:
            bodyupdates.add(None)
        return bodyupdates

    def emit(self, emitter):
        if self.count.code[-1] is _EXPRREF: # TODO more generic code
            count = self.count # since the memory cell is already within the range.
        else:
            count = self.count % (1 << emitter.cellsize)

        if emitter.debugging:
            emitter.dumpcomplex(self)

        var = emitter.newvariable('loopcnt')
        emitter.write('for (%s = %s; %s > 0; --%s) {' % (var, count, var, var))
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'Repeat[%r; %s]' % (self.count, ComplexNode.__repr__(self)[1:-1])

class While(ComplexNode):
    def __init__(self, cond=None, children=[]):
        ComplexNode.__init__(self, children)
        if cond is None:
            self.cond = MemNotEqual(0, 0)
        else:
            self.cond = cond

    def __nonzero__(self):
        # infinite loop should return True, even if there are no children.
        return bool(self.cond)

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.cond = self.cond.movepointer(offset)

    def withmemory(self, map):
        # updates condition only if the loop will be never executed.
        newcond = self.cond.withmemory(map)
        if isinstance(newcond, Never): self.cond = newcond

    def offsets(self):
        if self.stride() == 0:
            return 0
        else:
            return None

    def prereferences(self):
        bodyrefs = self.bodyprereferences()
        stride = self.stride()
        if bodyrefs and stride != 0:
            bodyrefs.add(None)
        return bodyrefs | self.cond.references()

    def postreferences(self):
        bodyrefs = self.bodypostreferences()
        stride = self.stride()
        if bodyrefs and stride != 0:
            bodyrefs.add(None)
        return bodyrefs | self.cond.references()

    def preupdates(self):
        bodyupdates = self.bodypreupdates()
        stride = self.stride()
        if bodyupdates and stride != 0:
            bodyupdates.add(None)
        return bodyupdates

    def postupdates(self):
        bodyupdates = self.bodypostupdates()
        stride = self.stride()
        if bodyupdates and stride != 0:
            bodyupdates.add(None)
        return bodyupdates

    def returns(self):
        return not isinstance(self.cond, Always)

    def emit(self, emitter):
        if emitter.debugging:
            emitter.dumpcomplex(self)

        if isinstance(self.cond, Always) and len(self) == 0:
            emitter.write('while (1); /* infinite loop */')
        else:
            emitter.write('while (%s) {' % self.cond)
            emitter.indent()
            for child in self:
                child.emit(emitter)
            emitter.dedent()
            emitter.write('}')

    def __repr__(self):
        return 'While[%r; %s]' % (self.cond, ComplexNode.__repr__(self)[1:-1])


class Emitter(object):
    def __init__(self, compiler, debugging=False):
        self.compiler = compiler
        self.debugging = debugging

        self.nindents = 0
        self.nextvars = {} 

    def __getattr__(self, name):
        return getattr(self.compiler, name)

    def newvariable(self, prefix):
        index = self.nextvars.get(prefix, 0)
        self.nextvars[prefix] = index + 1

        name = prefix + str(index)
        self.write('int %s;' % name)
        return name

    def dumpcomplex(self, node):
        stride = node.stride()
        if stride is None:
            self.write('// stride: unknown')
        elif stride != 0:
            self.write('// stride: %s' % stride)

        return # TODO
        updates = node.updates()
        updatesmore = None in updates
        updates.discard(None)
        updates = ' '.join(map(str, sorted(updates)))
        if updatesmore:
            self.write('// clobbers: %s (and possibly more)' % updates)
        elif updates:
            self.write('// clobbers: %s' % updates)

    def write(self, line):
        print '\t' * self.nindents + line

    def indent(self):
        self.nindents += 1

    def dedent(self):
        self.nindents -= 1

class Transformer(object):
    def __init__(self, target):
        assert isinstance(target, list)
        self.target = target
        self.cursormin = 0
        self.cursormax = 0

    def __iter__(self):
        return self

    def next(self):
        if self.cursormax >= len(self.target):
            raise StopIteration
        self.cursormin = self.cursormax
        self.cursormax += 1
        return self.cursormin, self.target[self.cursormin]

    def prepend(self, *items):
        self.target[self.cursormin:self.cursormin] = items
        self.cursormax += len(items)

    def append(self, *items):
        self.target[self.cursormax:self.cursormax] = items
        self.cursormax += len(items)

    def replace(self, *items):
        self.target[self.cursormin:self.cursormax] = items
        nitems = len(items)
        self.cursormax = self.cursormin + nitems

    def truncate(self):
        del self.target[self.cursormax:]

class Compiler(object):
    def __init__(self, cellsize=8):
        self.cellsize = cellsize

    def parse(self, fp):
        nodestack = [Program()]

        def flush(parent, changes, offset):
            for k, v in changes.items():
                if v != 0: parent.append(AdjustMemory(k, v))
            if offset != 0: parent.append(MovePointer(offset))

        changes = {}
        offset = 0
        for lineno, line in enumerate(fp):
            for ch in line:
                if ch == '+':
                    changes[offset] = changes.get(offset, 0) + 1
                elif ch == '-':
                    changes[offset] = changes.get(offset, 0) - 1
                elif ch == '>':
                    offset += 1
                elif ch == '<':
                    offset -= 1
                elif ch in '.,[]':
                    flush(nodestack[-1], changes, offset)
                    changes = {}
                    offset = 0

                    if ch == '.':
                        nodestack[-1].append(Output(Expr[0]))
                    elif ch == ',':
                        nodestack[-1].append(Input(0))
                    elif ch == '[':
                        nodestack.append(While())
                    else:
                        if len(nodestack) < 2:
                            raise ValueError('Not matching ] at line %d' % (lineno+1))
                        loop = nodestack.pop()
                        nodestack[-1].append(loop)

        flush(nodestack[-1], changes, offset)
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    def optimize(self, node):
        node = self.optimize_simpleloop(node)
        node = self.optimize_initialmemory(node)
        node = self.optimize_propagate(node)
        node = self.optimize_simpleloop(node)
        node = self.optimize_moreloop(node)
        node = self.optimize_propagate(node)
        node = self.optimize_stdlib(node)
        return node

    # general node cleanup routine. it does the following jobs:
    # - removes every no-op nodes, including If[False; ...] and k+=0.
    # - flattens Repeat[num; ...] node with all memory ops to parent.
    # - flattens If[True; ...] node to parent.
    # - merges MovePointer[] nodes as much as possible, and adjusts
    #   other nodes accordingly.
    # - removes every (dead) nodes after non-returning node.
    #
    # this is not recursive, and intended to be called in the end of other
    # optimization passes.
    def cleanup(self, node):
        if not isinstance(node, ComplexNode):
            return node

        offsets = 0
        tr = Transformer(node)
        for i, cur in tr:
            if not cur: # remove no-op
                tr.replace()
                continue

            cur.movepointer(offsets)
            ioffsets = cur.offsets()
            if ioffsets is not None:
                offsets += ioffsets

            if isinstance(cur, MovePointer):
                tr.replace()
                continue

            if isinstance(cur, If):
                if isinstance(cur.cond, Always):
                    tr.replace(*cur)

            elif isinstance(cur, Repeat):
                hasset = False
                for inode in cur:
                    if isinstance(inode, SetMemory):
                        if not inode.value.simple(): break
                        hasset = True
                    elif isinstance(inode, AdjustMemory):
                        if not inode.delta.simple(): break
                    else:
                        break

                else:
                    for inode in cur:
                        if isinstance(inode, AdjustMemory):
                            inode.delta *= cur.count
                    if hasset:
                        # cannot flatten, but we can turn it into If[]
                        tr.replace(If(ExprNotEqual(cur.count, 0), cur[:]))
                    else:
                        tr.replace(*cur)

            # if this command doesn't return, ignore all nodes after it.
            if not node[i-1].returns():
                tr.truncate()
                offsets = 0

        if offsets != 0:
            node.append(MovePointer(offsets))

        return node

    # adds redundant SetMemory nodes for later passes. other passes don't know
    # about initial memory contents, so it has to add such information explicitly.
    def optimize_initialmemory(self, node):
        if not isinstance(node, Program):
            return node

        offsets = 0
        changed = set([None]) # for getting rid of None
        tr = Transformer(node)
        for i, cur in tr:
            refs = _setmovepointer(cur.prereferences(), offsets)
            updates = _setmovepointer(cur.preupdates(), offsets)

            zerorefs = set(refs) - changed
            if zerorefs:
                tr.prepend(*[SetMemory(j - offsets, 0) for j in zerorefs])
                changed.update(zerorefs)
            changed.update(updates)

            ioffsets = cur.offsets()
            if ioffsets is None: break
            offsets += ioffsets

        return node

    # tries to convert various loops into more specific form:
    # - While[p[x]!=v; ...] with offsets=0, which adjusts cell 0 by const amount.
    #   this node will be replaced by Repeat[numrepeat; ...]
    # - While[p[x]!=v; ...] with offsets=0, which sets cell 0 to zero.
    #   this node will be replaced by If[p[x]!=v; ...].
    # - While[p[0]!=v; MovePointer[y]], where y is const.
    #   this nodes will be replaced by SeekMemory[p[y*k]!=v].
    def optimize_simpleloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 1 << self.cellsize

        for i in xrange(len(node)):
            if isinstance(node[i], ComplexNode):
                node[i] = self.optimize_simpleloop(node[i])

        tr = Transformer(node)
        for i, cur in tr:
            if not isinstance(cur, While): continue
            if not isinstance(cur.cond, MemNotEqual): continue

            target = cur.cond.target
            value = cur.cond.value

            if target == 0 and len(cur) == 1 and isinstance(cur[0], MovePointer):
                tr.replace(SeekMemory(0, cur[0].offset, value))
                continue

            if cur.offsets() != 0: continue

            flag = True # whether Repeat[] is applicable
            cell = Expr()
            mode = 0 # 0:adjust, 1:set, -1:unknown

            for inode in cur:
                if isinstance(inode, AdjustMemory):
                    if inode.offset == target:
                        cell += inode.delta
                elif isinstance(inode, SetMemory):
                    if inode.offset == target:
                        cell = inode.value
                        mode = 1
                else:
                    if not inode.pure():
                        flag = False
                    if inode.offsets() != 0:
                        flag = False
                        mode = -1

                    if flag:
                        updates = inode.preupdates()
                        if None in updates or target in updates:
                            flag = False
                            mode = -1

                if flag:
                    refs = inode.prereferences() - inode.preupdates()
                    if None in refs or target in refs:
                        flag = False # references target, cannot use Repeat[]

            if mode < 0 or not cell.simple(): continue
            delta = (value - int(cell)) % overflow

            if mode > 0:
                if delta == 0:
                    # XXX SetMemory is added temporarily; we should implement
                    # SSA-based optimizer and it will recognize them across basic blocks
                    tr.replace(If(cur.cond, cur[:]), SetMemory(target, value))
                else:
                    infloop = While(Always())
                    if not cur.pure(): # e.g. +[.[-]+]
                        infloop.extend(cur)
                    tr.replace(infloop)

            elif flag:
                # let w be the overflow value, which is 256 for char etc.
                # then there are three cases in the following code:
                #     i = 0; for (j = 0; i != x; ++j) i += m;
                #
                # 1. if m = 0, it loops forever.
                # 2. otherwise, the condition j * m = x (mod w) must hold.
                #    let u * m + v * w = gcd(m,w), and
                #    1) if x is not a multiple of gcd(m,w), it loops forever.
                #    2) otherwise it terminates and j = u * (x / gcd(m,w)).
                #
                # we can calculate u and gcd(m,w) in the compile time, but
                # x is not (yet). so we shall add simple check for now.

                if delta == 0:
                    tr.replace(While(Always()))
                    continue

                u, v, gcd = _gcdex(delta, overflow)
                diff = Expr[target] - value
                count = (u % overflow) * (diff // gcd)

                inodes = [inode for inode in cur
                          if not (isinstance(inode, (SetMemory, AdjustMemory)) and
                                  inode.offset == target)]

                result = []
                if gcd > 1: 
                    # no need to check if x is a multiple of gcd(m,w) (=1).
                    result.append(If(ExprNotEqual(diff % gcd, 0),
                                     [While(Always())]))
                if inodes:
                    # don't emit Repeat[] if [-] or [+] is given.
                    result.append(Repeat(count, inodes))
                result.append(SetMemory(target, value))
                tr.replace(*result)

        return self.cleanup(node)

    # extensive loop optimization. it calculates repeat count if possible and
    # tries to convert them into For[].
    def optimize_moreloop(self, node):
        return node

    # propagates cell references and constants as much as possible.
    # requires minptrloops pass for optimal processing. otherwise MovePointer
    # will act as memory blocker.
    def optimize_propagate(self, node):
        if not isinstance(node, ComplexNode):
            return node

        backrefs = {}
        usedrefs = {}
        substs = {} # only for simple one, unless some vars are not current

        tr = Transformer(node)
        for i, cur in tr:
            cur.withmemory(substs)

            alters = mergable = False
            offset = None
            refs = []
            if isinstance(cur, Nop):
                pass
            elif isinstance(cur, SetMemory):
                alters = mergable = True
                offset = cur.offset
                if cur.value.simple():
                    substs[offset] = cur.value
                else:
                    try: del substs[offset]
                    except: pass
            elif isinstance(cur, AdjustMemory):
                alters = mergable = True
                offset = cur.offset
                if offset in substs:
                    substs[offset] += cur.delta
                    if substs[offset].simple():
                        # replace with equivalent SetMemory node.
                        cur = SetMemory(offset, substs[offset])
                        tr.replace(cur)
                    else:
                        del substs[offset]
            elif isinstance(cur, Input):
                alters = True
                offset = cur.offset
                try: del substs[offset]
                except: pass
            elif isinstance(cur, Output):
                pass
            else: # MovePointer, While etc.
                tr.replace(self.optimize_propagate(cur))
                backrefs.clear()
                usedrefs.clear()
                substs.clear()
                if isinstance(cur, (While, If)) and isinstance(cur.cond, MemNotEqual):
                    substs[cur.cond.target] = cur.cond.value
                elif isinstance(cur, SeekMemory):
                    substs[cur.target] = cur.value

            refs = cur.postreferences()
            merged = False
            if alters:
                if not mergable:
                    # prohibit next merging attempt.
                    try: del backrefs[offset]
                    except: pass
                else:
                    # we can merge node[target] and node[i] if:
                    # - no operation has changed cell k between them. (thus such target
                    #   is backrefs[offset], as it is updated after change)
                    # - no operation has referenced the target cell between them.
                    #   node[target] itself could reference that cell.
                    # - no operation has changed cell(s) referenced by value.
                    #   similar to above, node[target] is excluded from this rule.
                    if offset in backrefs:
                        target = backrefs[offset]
                        if target >= usedrefs.get(offset, -1) and \
                                all(target >= backrefs.get(ioffset, -1) for ioffset in refs):
                            if isinstance(cur, AdjustMemory):
                                if isinstance(node[target], SetMemory):
                                    node[target].value += cur.delta
                                else:
                                    node[target].delta += cur.delta
                                if not node[target]:
                                    node[target] = Nop()
                            else:
                                node[target] = cur
                            tr.replace()
                            merged = True

                    if not merged:
                        backrefs[offset] = i

            if not merged:
                target = i
            for ioffset in refs:
                usedrefs[ioffset] = target

        return self.cleanup(node)

    # XXX proper name
    def optimize_convarray(self, node):
        return node

    # dead code elimination, sorta.
    def optimize_removedead(self, node):
        if not isinstance(node, ComplexNode):
            return node

    # converts common idioms to direct C library call.
    # - merges Output[] nodes into OutputConst[] node as much as possible.
    def optimize_stdlib(self, node):
        if not isinstance(node, ComplexNode):
            return node

        laststr = []
        tr = Transformer(node)
        for i, cur in tr:
            if isinstance(cur, Output) and cur.expr.simple():
                tr.replace()
                laststr.append(chr(int(cur.expr) & 0xff))
            elif isinstance(cur, OutputConst):
                tr.replace()
                laststr.append(cur.str)
            elif not isinstance(cur, (Input, SetMemory, AdjustMemory, MovePointer)):
                tr.replace(self.optimize_stdlib(cur))
                if laststr:
                    tr.prepend(OutputConst(''.join(laststr)))
                    laststr = []

        if laststr:
            node.append(OutputConst(''.join(laststr)))

        return node

    def emit(self, node, debugging=False):
        node.emit(Emitter(self, debugging))


def usage(progname):
    print >>sys.stderr, '''\
Esotope Brainfuck compiler
Copyright (c) 2009, Kang Seonghoon.

Usage: %s [options] filename  (from file)
       %s [options] -         (from stdin)

Options:
-h, --help
    Shows this message.
-s BITS, --cellsize BITS
    Sets the size of each memory size. BITS can be 8, 16 or 32, and
    defaults to 8.
--debug
    Enables debugging output (as C comment) in the code.

For more information please visit http://esotope-bfc.googlecode.com/.
''' % (progname, progname)

def main(argv):
    try:
        opts, args = getopt.getopt(argv[1:], 'hs:',
                ['help', 'cellsize=', 'debug'])
    except getopt.GetoptError, err:
        print >>sys.stderr, 'Error: %s' % err
        print >>sys.stderr, 'Type "%s --help" for usage.' % argv[0]
        return 1

    cellsize = 8
    debugging = False
    for opt, arg in opts:
        if opt in ('-h', '--help'):
            usage(argv[0])
            return 0
        elif opt in ('-s', '--cellsize'):
            try:
                cellsize = int(arg)
                if cellsize not in (8, 16, 32): raise ValueError
            except:
                print >>sys.stderr, 'Error: Invalid cell size %r.' % arg
                return 1
        elif opt == '--debug':
            debugging = True
        else:
            assert False

    if not args:
        print >>sys.stderr, 'Type "%s --help" for usage.' % argv[0]
        return 1

    if args[0] == '-':
        fp = sys.stdin
    else:
        fp = open(args[0], 'r')

    compiler = Compiler(cellsize=cellsize)
    node = compiler.parse(fp)
    node = compiler.optimize(node)
    compiler.emit(node, debugging)
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

