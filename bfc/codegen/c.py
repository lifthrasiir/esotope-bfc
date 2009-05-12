# This is a part of Esotope Brainfuck-to-C Compiler.

import sys
import cStringIO as stringio

class Emitter(object):
    def __init__(self, compiler, debugging=False):
        self.compiler = compiler
        self.debugging = debugging

        self.declbuf = stringio.StringIO()
        self.buf = stringio.StringIO()
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

    __del__ = flush

    def indent(self):
        self.nindents += 1

    def dedent(self):
        self.nindents -= 1

