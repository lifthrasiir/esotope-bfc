#!/usr/bin/env python
# Esotope Brainfuck-to-C Compiler
# Copyright (c) 2009, Kang Seonghoon.

import sys
from collections import namedtuple
from cStringIO import StringIO

try: import psyco; psyco.full()
except ImportError: pass

_reprmap = [('\\%03o', '%c')[32 <= i < 127] % i for i in xrange(256)]
_reprmap[0] = '\\0'; _reprmap[9] = '\\t'; _reprmap[10] = '\\n'; _reprmap[13] = '\\r'
_reprmap[34] = '\\"'; _reprmap[39] = '\''; _reprmap[92] = '\\\\'
def _addslashes(s):
    return ''.join(_reprmap[ord(i)] for i in s)


_EXPRNEG = '_'
_EXPRREF = '@'
_EXPRADD = '+'
_EXPRMUL = '*'
_EXPRARITYMAP = {_EXPRNEG: 1, _EXPRREF: 1, _EXPRADD: 2, _EXPRMUL: 2}

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
            if c is _EXPRADD:
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

            elif c is _EXPRNEG:
                arg = stack.pop()
                if len(arg) == 1: result = [-arg[0]]
                elif arg[-1] is _EXPRNEG: result = arg[:-1]
                else: result = arg + [_EXPRNEG]

            elif c is _EXPRREF:
                arg = stack.pop()
                result = arg + [_EXPRREF]

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
            if c is _EXPRADD:
                rhs = stack.pop(); lhs = stack.pop()
                if rhs.startswith('-'):
                    stack.append('(%s%s)' % (lhs, rhs))
                else:
                    stack.append('(%s+%s)' % (lhs, rhs))
            elif c is _EXPRMUL:
                rhs = stack.pop(); lhs = stack.pop()
                stack.append('(%s*%s)' % (lhs, rhs))
            elif c is _EXPRNEG:
                arg = stack.pop()
                stack.append('-%s' % arg)
            elif c is _EXPRREF:
                arg = stack.pop()
                stack.append('mptr[%s]' % arg)
            else:
                stack.append(str(c))
        return stack[-1]


class Node(object):
    # returns False if it is a no-op. minptrmoves pass will remove such no-ops.
    def __nonzero__(self): return True

    # returns False if it does an input or output, thus cannot be reordered.
    def pure(self): return True

    # moves all memory references in it by offset.
    # if it is not possible (like WhileNotEqual) canmovepointer should return False.
    def canmovepointer(self, offset): return False
    def movepointer(self, offset): raise RuntimeError('not implemented')

    # specifies what this node does. optimizer assumes it does:
    # - changes the pointer by node.offsets().
    # - references (at least) all memory cells in node.references().
    # - updates (at least) all memory cells in node.updates().
    #
    # node.offsets() can return Expr object, or None if uncertain.
    # node.references() and node.updates() is a set containing memory offset
    # relative to the final (after moved by node.offsets()) pointer.
    # if the set contains None, it can reference or update other unspecificed cells.
    def offsets(self): return 0
    def references(self): return set()
    def updates(self): return set()

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
        emitter.write('char mem[30000], *mptr = mem;')
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

class IfNotEqual(ComplexNode):
    def __init__(self, target, value=0, children=[]):
        ComplexNode.__init__(self, children)
        self.target = target
        self.value = value

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.target += offset

    def offsets(self):
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return set([self.target]) | ComplexNode.references(self)

    def updates(self):
        return set([self.target]) | ComplexNode.updates(self)

    def emit(self, emitter):
        if self.value == 0:
            emitter.write('if (mptr[%s]) {' % self.target)
        else:
            emitter.write('if (mptr[%s] != %s) {' % (self.target, self.value))
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        if self.value == 0:
            return 'If[mptr[%r]; %s]' % (self.target, ComplexNode.__repr__(self)[1:-1])
        else:
            return 'If[mptr[%r]!=%r; %s]' % (self.target, self.value,
                    ComplexNode.__repr__(self)[1:-1])

class WhileNotEqual(ComplexNode):
    def __init__(self, target, value=0, children=[]):
        ComplexNode.__init__(self, children)
        self.target = target
        self.value = value

    def movepointer(self, offset):
        ComplexNode.movepointer(self, offset)
        self.target += offset

    def offsets(self):
        if ComplexNode.offsets(self) == 0:
            return 0
        else:
            return None

    def references(self):
        return set([self.target]) | ComplexNode.references(self)

    def updates(self):
        return set([self.target]) | ComplexNode.updates(self)

    def emit(self, emitter):
        emitter.write('while (mptr[%s]) {' % self.target)
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def emit(self, emitter):
        if self.value == 0:
            emitter.write('while (mptr[%s]) {' % self.target)
        else:
            emitter.write('while (mptr[%s] != %s) {' % (self.target, self.value))
        emitter.indent()
        for child in self:
            child.emit(emitter)
        emitter.dedent()
        emitter.write('}')

    def __repr__(self):
        if self.value == 0:
            return 'While[mptr[%r]; %s]' % (self.target, ComplexNode.__repr__(self)[1:-1])
        else:
            return 'While[mptr[%r]!=%r; %s]' % (self.target, self.value,
                    ComplexNode.__repr__(self)[1:-1])


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
                        nodestack.append(WhileNotEqual(0))
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
        node = self.optimize_minptrmoves(node)
        node = self.optimize_onceuponatime(node)
        node = self.optimize_propagate(node)
        node = self.optimize_simpleloop(node)
        node = self.optimize_moreloop(node)
        node = self.optimize_propagate(node)
        node = self.optimize_stdlib(node)
        return node

    # minimizes number of MovePointer nodes.
    def optimize_minptrmoves(self, node):
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
                result.append(self.optimize_minptrmoves(cur))
                replace(*result)
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
            if isinstance(cur, AdjustMemory) and cur.offset + offsets not in changed:
                replace(SetMemory(cur.offset, cur.delta))
            elif isinstance(cur, (WhileNotEqual, IfNotEqual)) and \
                    cur.target + offsets not in changed:
                replace() # while(0) { ... } etc.

            ioffsets = cur.offsets()
            if ioffsets is None: break
            offsets += ioffsets

            changed.update(j + offsets for j in cur.updates() if j is not None)

        while node and isinstance(node[-1], MovePointer):
            del node[-1]
        return node

    # tries to optimize simple loops:
    # - WhileNotEqual[...] with offsets=0, no I/O, changes cell 0 by -1 or +1 within it.
    #   every arguments of memory operation in it should be simple.
    # - WhileNotEqual[...] with offsets=0, no I/O, sets cell 0 to 0 within.
    #
    # this pass is for optimizing very common cases, like multiplication loops.
    # moreloop pass will turn other cases into for loops.
    def optimize_simpleloop(self, node):
        if not isinstance(node, ComplexNode):
            return node

        overflow = 256 # XXX hard-coded, must be the power of 2

        inodes = []
        for i, cur, replace in node.transforming():
            if isinstance(cur, WhileNotEqual) and cur.offsets() == 0:
                # check constraints.
                cell = 0
                cellset = None
                targetnode = None
                hasset = False # if set we should cover loop with IfNotEqual[].
                complex = False # complex loop is ignored unless it's conditional.
                multiplier = None

                for inode in cur:
                    if isinstance(inode, SetMemory):
                        if not inode.value.simple():
                            complex = True
                        if inode.offset == cur.target:
                            cell = inode.value
                            cellset = True
                            targetnode = inode
                        hasset = True
                    elif isinstance(inode, AdjustMemory):
                        if not inode.delta.simple():
                            complex = True
                        if inode.offset == cur.target:
                            cell += inode.delta
                            targetnode = inode
                    else:
                        if not inode.pure():
                            complex = True
                        if isinstance(inode, ComplexNode):
                            break
                else:
                    if cellset:
                        if cell == 0:
                            multiplier = 1
                    elif not complex:
                        # XXX use cur.value for correct loop count
                        if cell == 1:
                            multiplier = overflow - Expr[cur.target]
                        elif cell == -1:
                            multiplier = Expr[cur.target]

                if multiplier is not None:
                    result = []
                    for inode in cur:
                        if inode is targetnode: continue
                        if isinstance(inode, AdjustMemory):
                            inode.delta *= multiplier
                        result.append(inode)

                    if hasset: result = [IfNotEqual(cur.target, children=result)]
                    result.append(SetMemory(cur.target, cur.value))
                    replace(*result)
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
            impure = mergable = False
            offset = None
            refs = []
            if isinstance(cur, SetMemory):
                impure = mergable = True
                offset = cur.offset
                value = cur.value = cur.value.withmemory(substs)
                refs = value.references()
                if value.simple():
                    substs[offset] = value
                else:
                    try: del substs[offset]
                    except: pass
            elif isinstance(cur, AdjustMemory):
                impure = mergable = True
                offset = cur.offset
                value = cur.delta = cur.delta.withmemory(substs)
                if offset in substs:
                    substs[offset] += value
                    if substs[offset].simple():
                        # replace with equivalent SetMemory node.
                        cur = SetMemory(offset, substs[offset])
                        value = cur.value
                        replace(cur)
                    else:
                        del substs[offset]
                refs = value.references()
            elif isinstance(cur, Input):
                impure = True
                offset = cur.offset
                try: del substs[offset]
                except: pass
            elif isinstance(cur, Output):
                expr = cur.expr = cur.expr.withmemory(substs)
                refs = expr.references()
            else: # MovePointer, WhileNotEqual etc.
                replace(self.optimize_propagate(cur))
                backrefs.clear()
                usedrefs.clear()
                substs.clear()
                if isinstance(cur, (WhileNotEqual, IfNotEqual)):
                    substs[cur.target] = cur.value

            merged = False
            if impure:
                if not mergable:
                    # prohibit next merging attempt.
                    try: del backrefs[offset]
                    except: pass
                else:
                    if offset in backrefs:
                        # we can merge node[target] and node[i] if:
                        # - no operation has changed cell k between them. (thus such target
                        #   is backrefs[offset], as it is updated after change)
                        # - no operation has referenced cell k between them. it includes
                        #   node[target] which is self-reference (like a = a + 4).
                        # - no operation has changed cell k' which is referenced by v.
                        #   it includes node[target] too, if v references target k.
                        target = backrefs[offset]
                        if target > usedrefs.get(offset, -1) and \
                                all(target > backrefs.get(ioffset, -1) for ioffset in refs):
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

    compiler = Compiler()
    node = compiler.parse(file(argv[1], 'r'))
    node = compiler.optimize(node)
    node.emit(Emitter())
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv))

