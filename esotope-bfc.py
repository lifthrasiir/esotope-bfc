#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
from cStringIO import StringIO

try: import psyco; psyco.full()
except ImportError: pass

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
                stack.append('mptr[%s]' % arg)
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
            return 'mptr[%s]' % self.target
        else:
            return 'mptr[%s] != %s' % (self.target, self.value)

    def __repr__(self):
        if self.value == 0:
            return 'mptr[%r]' % self.target
        else:
            return 'mptr[%r]!=%r' % (self.target, self.value)

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
    # if it is not possible (like While) canmovepointer should return False.
    def canmovepointer(self, offset): return False
    def movepointer(self, offset): raise RuntimeError('not implemented')

    # propagates known memory cells given.
    def withmemory(self, map): pass

    # specifies what this node does. optimizer assumes it does:
    #
    # - changes the pointer by node.offsets().
    #   node.offsets() can return Expr object, or None if uncertain.
    #
    # - references some or all memory cells in node.references().
    #   memory offsets here are relative to the final pointer, after
    #   changed by node.offsets(). if it may reference other cells unspecified
    #   it should contain None.
    #
    # - updates some or all memory cells in node.updates().
    #   this is similar to node.references(). in reality it behaves like
    #   "clobber" list, as even no memory cells have to be updated.
    #
    # - will run forever if node.returns() is False.
    #   there could be an infinite loop with node.returns() = True, though.

    def offsets(self): return 0
    def references(self): return set()
    def updates(self): return set()
    def returns(self): return True

class ComplexNode(Node, list):
    def __nonzero__(self):
        return len(self) > 0

    def canmovepointer(self, offset):
        if offset == 0: return True
        if self.offsets() != 0: return False
        return all(child.canmovepointer(offset) for child in self)

    def movepointer(self, offset):
        if offset != 0:
            for child in self: child.movepointer(offset)

    def pure(self):
        return all(child.pure() for child in self)

    def offsets(self):
        offsets = 0
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None: return None
            offsets += ioffsets
        return offsets

    def references(self):
        offsets = 0
        refs = []
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None:
                # invalidates prior updates, but not later nor current.
                offsets = 0
                refs = [None]
            refs.extend(i if i is None else i + offsets for i in child.references())

        # should return memory references relative to final pointer.
        return set(i if i is None else i - offsets for i in refs)

    def updates(self):
        offsets = 0
        updates = []
        for child in self:
            ioffsets = child.offsets()
            if ioffsets is None:
                offsets = 0
                updates = [None]
            updates.extend(i if i is None else i + offsets for i in child.updates())

        return set(i if i is None else i - offsets for i in updates)

    def transforming(self):
        replacement = [] # to be modifiable in the closure
        def replace(*nodes): replacement[:] = nodes

        i = 0
        while i < len(self):
            replacement[:] = [self[i]]
            yield i, self[i], replace
            self[i:i+1] = replacement
            i += len(replacement)

    def __repr__(self):
        return list.__repr__(self)

class Program(ComplexNode):
    def emit(self, emitter):
        emitter.write('/* generated by esotope-bfc */')
        emitter.write('#include <stdio.h>')
        emitter.write('unsigned char mem[30000], *mptr = mem;')
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

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset
        self.value = self.value.movepointer(offset)

    def withmemory(self, map):
        self.value = self.value.withmemory(map)

    def references(self):
        return self.value.references()

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        emitter.write('mptr[%d] = %s;' % (self.offset, self.value))

    def __repr__(self):
        return '%d=%r' % (self.offset, self.value)

class AdjustMemory(Node):
    def __init__(self, offset, delta):
        self.offset = offset
        self.delta = Expr(delta)

    def __nonzero__(self):
        return self.delta != 0

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset
        self.delta = self.delta.movepointer(offset)

    def withmemory(self, map):
        self.delta = self.delta.withmemory(map)

    def references(self):
        return set([self.offset]) | self.delta.references()

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        if self.delta < 0:
            emitter.write('mptr[%d] -= %s;' % (self.offset, -self.delta))
        elif self.delta != 0:
            emitter.write('mptr[%d] += %s;' % (self.offset, self.delta))

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

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        pass # no change

    def offsets(self):
        return self.offset

    def emit(self, emitter):
        if self.offset < 0:
            emitter.write('mptr -= %s;' % -self.offset)
        elif self.offset != 0:
            emitter.write('mptr += %s;' % self.offset)

    def __repr__(self):
        return '@%r' % self.offset

class Input(Node):
    def __init__(self, offset):
        self.offset = offset

    def pure(self):
        return False

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        self.offset += offset

    def updates(self):
        return set([self.offset])

    def emit(self, emitter):
        emitter.write('mptr[%s] = getchar();' % self.offset)

    def __repr__(self):
        return 'Input[%r]' % self.offset

class Output(Node):
    def __init__(self, expr):
        self.expr = expr

    def pure(self):
        return False

    def canmovepointer(self, offset):
        return True

    def withmemory(self, map):
        self.expr = self.expr.withmemory(map)

    def references(self):
        return self.expr.references()

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

    def canmovepointer(self, offset):
        return True

    def movepointer(self, offset):
        pass # does nothing

    def emit(self, emitter):
        for line in self.str.splitlines(True):
            emitter.write('printf("%s");' % _addslashes(line))

    def __repr__(self):
        return 'OutputConst[%r]' % self.str

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
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return ComplexNode.references(self) | self.cond.references()

    def updates(self):
        return ComplexNode.updates(self)

    def emit(self, emitter):
        emitter.write('if (%s) {' % self.cond)
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        return 'If[%r; %s]' % (self.cond, ComplexNode.__repr__(self)[1:-1])

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
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return ComplexNode.references(self) | self.cond.references()

    def updates(self):
        return ComplexNode.updates(self)

    def returns(self):
        return not isinstance(self.cond, Always)

    def emit(self, emitter):
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
    def __init__(self):
        self.nindents = 0

    def write(self, line):
        print '\t' * self.nindents + line

    def indent(self):
        self.nindents += 1

    def dedent(self):
        self.nindents -= 1

class Compiler(object):
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
        node = self.optimize_cleanup(node)
        node = self.optimize_onceuponatime(node)
        node = self.optimize_propagate(node)
        node = self.optimize_simpleloop(node)
        node = self.optimize_moreloop(node)
        node = self.optimize_propagate(node)
        node = self.optimize_cleanup(node)
        node = self.optimize_stdlib(node)
        return node

    # general node cleanup routine. it does the following jobs:
    # - removes every no-op nodes.
    # - flattens If[True; ...] node to parent.
    # - merges MovePointer[] nodes as much as possible, and adjusts
    #   other nodes accordingly.
    # - removes every (dead) nodes after non-returning node.
    def optimize_cleanup(self, node):
        if not isinstance(node, ComplexNode):
            return node

        offset = 0
        for i, cur, replace in node.transforming():
            if not cur: # remove no-op
                replace()
            elif isinstance(cur, MovePointer):
                offset += cur.offset
                replace()
            else:
                result = []
                if cur.canmovepointer(offset):
                    cur.movepointer(offset)
                else:
                    # movepointer failed, flush current MovePointer node before it
                    if offset != 0: result.append(MovePointer(offset))
                    offset = 0
                result.append(self.optimize_cleanup(cur))
                replace(*result)

                # if this command doesn't return, ignore all nodes after it.
                if not result[-1].returns():
                    del node[i+len(result):]
                    offset = 0
                    break

        if offset != 0:
            node.append(MovePointer(offset))

        return node

    # change first AdjustMemory nodes to SetMemory in the very first of program.
    # also removes the last (redundant) MovePointer if any.
    def optimize_onceuponatime(self, node):
        if not isinstance(node, Program):
            return node

        offsets = 0
        changed = set()
        for i, cur, replace in node.transforming():
            if isinstance(cur, AdjustMemory) and \
                    cur.offset + offsets not in changed:
                replace(SetMemory(cur.offset, cur.delta))
            elif isinstance(cur, (While, If)) and isinstance(cur.cond, MemNotEqual) and \
                    cur.cond.target + offsets not in changed:
                replace() # while(0) { ... } etc.

            ioffsets = cur.offsets()
            if ioffsets is None: break
            offsets += ioffsets

            changed.update(j + offsets for j in cur.updates() if j is not None)

        while node and isinstance(node[-1], MovePointer):
            del node[-1]
        return node

    # tries to optimize simple loops:
    # - While[mptr[x]!=v; ...] with offsets=0, no I/O nor complex memory ops,
    #   and adjust cell 0 by const amount within it.
    # - While[mptr[x]!=v; ...] with offsets=0, sets cell 0 to zero within it.
    #
    # this pass is for optimizing very common cases, like multiplication loops.
    # moreloop pass will turn other cases into for loops.
    def optimize_simpleloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 256 # XXX hard-coded

        inodes = []
        for i, cur, replace in node.transforming():
            if isinstance(cur, While) and isinstance(cur.cond, MemNotEqual) and \
                    cur.offsets() == 0:
                target = cur.cond.target
                value = cur.cond.value

                # check constraints.
                cell = 0
                cellset = None
                tobeignored = None
                mergable = True # may we merge the loop into parent?
                complex = False # complex loop is ignored unless it's conditional.
                multiplier = None

                for inode in cur:
                    if isinstance(inode, AdjustMemory):
                        if not inode.delta.simple():
                            complex = True
                        if inode.offset == target:
                            cell += inode.delta
                            tobeignored = inode
                    elif not isinstance(inode, Nop):
                        mergable = False
                        if isinstance(inode, SetMemory):
                            if not inode.value.simple():
                                complex = True
                            if inode.offset == target:
                                cell = inode.value
                                cellset = True
                                tobeignored = inode
                        else:
                            if not inode.pure():
                                complex = True
                            if isinstance(inode, ComplexNode):
                                break

                else:
                    delta = (value - int(cell)) % overflow
                    if cellset:
                        if delta == 0:
                            multiplier = 1
                            template = [If(cur.cond)]
                            result = template[0]
                        else:
                            replace(While(Always()))
                            continue
                    elif not complex:
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
                            replace(While(Always()))
                            continue

                        diff = Expr[target] - value

                        u, v, gcd = _gcdex(delta, overflow)
                        multiplier = (u % overflow) * (diff // gcd)

                        if mergable:
                            template = []
                            result = template
                        else:
                            template = [If(cur.cond)]
                            result = template[0]
                        if gcd != 1:
                            template.insert(0,
                                    If(ExprNotEqual(diff % gcd, 0), [While(Always())]))

                if multiplier is not None:
                    for inode in cur:
                        if inode is tobeignored: continue
                        if isinstance(inode, AdjustMemory):
                            inode.delta *= multiplier
                        result.append(inode)
                    template.append(SetMemory(target, value))
                    replace(*template)
                    continue

            if isinstance(cur, ComplexNode):
                replace(self.optimize_simpleloop(cur))

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

        for i, cur, replace in node.transforming():
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
                        replace(cur)
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
                replace(self.optimize_propagate(cur))
                backrefs.clear()
                usedrefs.clear()
                substs.clear()
                if isinstance(cur, (While, If)) and isinstance(cur.cond, MemNotEqual):
                    substs[cur.cond.target] = cur.cond.value

            refs = cur.references()
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
                            replace()
                            merged = True

                    if not merged:
                        backrefs[offset] = i

            if not merged:
                target = i
            for ioffset in refs:
                usedrefs[ioffset] = target

        return node

    # extensive loop optimization. it calculates repeat count if possible and
    # tries to convert them into For[].
    def optimize_moreloop(self, node):
        return node

    # converts common idioms to direct C library call.
    def optimize_stdlib(self, node):
        if not isinstance(node, ComplexNode):
            return node

        inodes = []
        laststr = []
        for inode in node:
            if isinstance(inode, Output) and inode.expr.simple():
                laststr.append(chr(int(inode.expr) & 0xff))
            elif isinstance(inode, OutputConst):
                laststr.append(inode.str)
            elif isinstance(inode, (Input, SetMemory, AdjustMemory, MovePointer)):
                inodes.append(inode) # doesn't affect string output
            else:
                if laststr:
                    inodes.append(OutputConst(''.join(laststr)))
                    laststr = []
                if isinstance(inode, ComplexNode):
                    inodes.append(self.optimize_stdlib(inode))
                else:
                    inodes.append(inode)
        if laststr:
            inodes.append(OutputConst(''.join(laststr)))
        node[:] = inodes
        return node

def main(argv):
    if len(argv) < 2:
        print >>sys.stderr, 'Usage: %s filename' % argv[0]
        return 1

    if argv[1] == '-':
        fp = sys.stdin
    else:
        fp = open(argv[1], 'r')

    compiler = Compiler()
    node = compiler.parse(fp)
    node = compiler.optimize(node)
    node.emit(Emitter())
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

