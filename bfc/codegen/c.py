# This is a part of Esotope Brainfuck Compiler.

import sys
import cStringIO as stringio

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.codegen.base import BaseGenerator

class Generator(BaseGenerator):
    def __init__(self, compiler):
        BaseGenerator.__init__(self, compiler)
        self.declbuf = stringio.StringIO()
        self.buf = stringio.StringIO()
        self.nextvars = {} 

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

        updates = node.postupdates()
        if updates:
            self.write('// clobbers: %r' % updates)

    def write(self, line):
        self.buf.write('\t' * self.nindents + line + '\n')

    def flush(self):
        sys.stdout.write(self.declbuf.getvalue())
        self.declbuf.reset()
        self.declbuf.truncate()

        sys.stdout.write(self.buf.getvalue())
        self.buf.reset()
        self.buf.truncate()

    ############################################################

    def adoptcond(self, cond):
        if isinstance(cond, Range):
            # p[x]~(...) actually means p[x+nW]~(...) for every integer n.
            # XXX sub-optimal algorithm
            cellsize = self.cellsize
            multiples = set()
            for min, max in cond.ranges:
                if min is not None: multiples.add(min >> cellsize)
                if max is not None: multiples.add((max-1) >> cellsize)
            realranges = [Between(0, cond.expr, (1 << cellsize) - 1)]
            for n in multiples:
                realranges.append(Range(cond.expr + (n << cellsize), *cond.ranges))
            return Conjunction(*realranges)
        elif isinstance(cond, Conjunction):
            return Conjunction(*map(self.adoptcond, cond))
        elif isinstance(cond, Disjunction):
            return Disjunction(*map(self.adoptcond, cond))
        else:
            return cond

    def _generateexpr(self, expr, prec=0):
        _generateexpr = self._generateexpr

        if isinstance(expr, ReferenceExpr):
            return 'p[%s]' % _generateexpr(expr.offset)

        if isinstance(expr, LinearExpr):
            result = []
            for v, k in expr[1:]:
                if v == -1: result.append('-%s' % _generateexpr(k, 1))
                elif v == 1: result.append('+%s' % _generateexpr(k, 1))
                else: result.append('%+d*%s' % (v, _generateexpr(k, 1)))
            if expr[0] != 0:
                result.append('%+d' % expr[0])

            if result:
                terms = ''.join(result).lstrip('+')
            else:
                terms = '0'
            if prec > 1 and len(result) > 1:
                terms = '(%s)' % terms
            return terms

        if isinstance(expr, MultiplyExpr):
            terms = '*'.join(_generateexpr(e, 2) for e in expr)
            if prec > 2 and len(expr) > 1: terms = '(%s)' % terms
            return terms

        if isinstance(expr, (DivisionExpr, ExactDivisionExpr)):
            terms = '%s/%s' % (_generateexpr(expr.lhs, 2), _generateexpr(expr.rhs, 2))
            if prec > 3: terms = '(%s)' % terms
            return terms

        if isinstance(expr, ModuloExpr):
            terms = '%s%%%s' % (_generateexpr(expr.lhs, 2), _generateexpr(expr.rhs, 2))
            if prec > 3: terms = '(%s)' % terms
            return terms

        assert not isinstance(expr, Expr)
        return str(expr)

    def generateexpr(self, expr):
        if isinstance(expr, Expr):
            return self._generateexpr(expr)
        else:
            return str(expr)

    def generatecond(self, cond):
        if isinstance(cond, Always):
            return '1'
        elif isinstance(cond, Never):
            return '0'
        elif isinstance(cond, Equal):
            if cond.value == 0:
                return '!' + self.generateexpr(cond.expr)
            else:
                return '%s == %d' % (self.generateexpr(cond.expr), cond.value)
        elif isinstance(cond, NotEqual):
            if cond.value == 0:
                return self.generateexpr(cond.expr)
            else:
                return '%s != %d' % (self.generateexpr(cond.expr), cond.value)
        elif isinstance(cond, Range):
            expr = self.generateexpr(cond.expr)
            terms = []
            for min, max in cond.ranges:
                if min is None:
                    terms.append('%s <= %d' % (expr, max))
                elif max is None:
                    terms.append('%d <= %s' % (min, expr))
                elif min == max:
                    terms.append('%s == %d' % (expr, min))
                else:
                    terms.append('(%d <= %s && %s <= %d)' % (min, expr, expr, max))
            if len(terms) == 1:
                return terms[0]
            else:
                return '(%s)' % ' || '.join(terms)
        elif isinstance(cond, Conjunction):
            return '(%s)' % ' && '.join(map(self.generateexpr, cond))
        elif isinstance(cond, Disjunction):
            return '(%s)' % ' || '.join(map(self.generateexpr, cond))
        else:
            assert False

    ############################################################

    def _formatadjust(self, ref, value):
        if isinstance(value, (int, long)) or value.simple():
            value = int(value)
            if value == 0:
                return ''
            elif value == 1:
                return '++%s' % ref
            elif value == -1:
                return '--%s' % ref

        posform = '%s += %s' % (ref, self.generateexpr(value))
        negform = '%s -= %s' % (ref, self.generateexpr(-value))
        if len(negform) < len(posform):
            return negform
        else:
            return posform

    _reprmap = [('\\%03o', '%c')[32 <= i < 127] % i for i in xrange(256)]
    _reprmap[0] = '\\0'; _reprmap[9] = '\\t'; _reprmap[10] = '\\n'; _reprmap[13] = '\\r'
    _reprmap[34] = '\\"'; _reprmap[39] = '\''; _reprmap[92] = '\\\\'
    def _addslashes(self, s, _reprmap=_reprmap):
        return ''.join(_reprmap[ord(i)] for i in s)

    def generate_Program(self, node):
        self.getcused = self.putcused = self.putsused = False
        self.write('static uint%d_t m[30000], *p = m;' % self.cellsize)
        self.write('int main(void) {')
        self.indent()

        returns = True
        genmap = self.genmap
        for child in node:
            genmap[type(child)](child)
            returns &= child.returns()

        if returns:
            self.write('return 0;')
        self.dedent()
        self.write('}')

        # build declarations
        self.declbuf.write('/* generated by esotope-bfc */\n')
        self.declbuf.write('#include <stdio.h>\n')
        self.declbuf.write('#include <stdint.h>\n')
        if self.getcused:
            self.declbuf.write('#define GETC() (fflush(stdout), fgetc(stdin))\n')
        if self.putcused:
            self.declbuf.write('#define PUTC(c) fputc(c, stdout)\n')
        if self.putsused:
            self.declbuf.write('#define PUTS(s) fwrite(s, 1, sizeof(s)-1, stdout)\n')

    def generate_Nop(self, node):
        pass # do nothing

    def generate_SetMemory(self, node):
        fullstmt = 'p[%d] = %s;' % (node.offset, self.generateexpr(node.value))
        shortstmt = self._formatadjust('p[%d]' % node.offset, node.delta) + ';'
        if len(shortstmt) < len(fullstmt):
            self.write(shortstmt)
        else:
            self.write(fullstmt)

    def generate_MovePointer(self, node):
        stmt = self._formatadjust('p', node.offset)
        if stmt: self.write(stmt + ';')

    def generate_Input(self, node):
        self.getcused = True
        self.write('p[%d] = GETC();' % node.offset)

    def generate_Output(self, node):
        self.putcused = True
        self.write('PUTC(%s);' % self.generateexpr(node.expr))

    def generate_OutputConst(self, node):
        self.putsused = True
        for line in node.str.splitlines(True):
            self.write('PUTS("%s");' % self._addslashes(line))

    def generate_SeekMemory(self, node):
        self.write('while (p[%d] != %d) %s;' % (node.target, node.value,
                self._formatadjust('p', node.stride)))

    def generate_If(self, node):
        if self.debugging:
            self.dumpcomplex(self)

        self.write('if (%s) {' % self.generatecond(self.adoptcond(node.cond)))
        self._generatenested(node)
        self.write('}')

    def generate_Repeat(self, node):
        count = node.count
        if count.simple() or not isinstance(count, ReferenceExpr): # TODO more generic code
            # the memory cell is already within the range, so no need to add modulo.
            count %= (1 << self.cellsize)

        if self.debugging:
            self.dumpcomplex(self)

        var = self.newvariable('loopcnt')
        self.write('for (%s = %s; %s > 0; --%s) {' %
                (var, self.generateexpr(count), var, var))
        self._generatenested(node)
        self.write('}')

    def generate_While(self, node):
        if self.debugging:
            self.dumpcomplex(self)

        if isinstance(node.cond, Always) and len(node) == 0:
            self.write('while (1); /* infinite loop */')
        else:
            self.write('while (%s) {' % self.generatecond(self.adoptcond(node.cond)))
            self._generatenested(node)
            self.write('}')

