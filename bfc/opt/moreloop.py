# This is a part of Esotope Brainfuck-to-C Compiler.

# extensive loop optimization. it calculates repeat count if possible and
# tries to convert them into For[].

from bfc.opt import OptimizerPass, Transformer

class MoreLoopPass(OptimizerPass):
    def transform(self, node):
        # TODO
        return node

