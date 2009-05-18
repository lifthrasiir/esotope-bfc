# This is a part of Esotope Brainfuck-to-C Compiler.

import bfc.nodes

class Generator(object):
    def __init__(self, compiler):
        self.compiler = compiler
        self.nindents = 0

        self.genmap = {}
        for name in dir(self):
            if not name.startswith('generate_'): continue
            try:
                self.genmap[getattr(bfc.nodes, name[9:])] = getattr(self, name)
            except AttributeError:
                pass

    def __del__(self):
        self.flush()

    def __getattr__(self, name):
        return getattr(self.compiler, name)

    def flush(self):
        raise NotImplemented

    def indent(self):
        self.nindents += 1

    def dedent(self):
        self.nindents -= 1

    def _generatenested(self, children):
        genmap = self.genmap
        self.indent()
        for child in children:
            genmap[type(child)](child)
        self.dedent()

    def generate(self, node):
        self.debugging = self.compiler.debugging
        self.genmap[type(node)](node)

