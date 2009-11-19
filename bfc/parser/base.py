# This is a part of Esotope Brainfuck Compiler.

class BaseParser(object):
    def __init__(self, compiler):
        self.compiler = compiler

    def __getattr__(self, name):
        return getattr(self.compiler, name)

    def parse(self, fp):
        raise NotImplementedError

