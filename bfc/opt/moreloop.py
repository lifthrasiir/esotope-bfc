# This is a part of Esotope Brainfuck Compiler.

from bfc.opt import BaseOptimizerPass, Transformer

class OptimizerPass(BaseOptimizerPass):
    # extensive loop optimization. it calculates repeat count if possible and
    # tries to convert them into For[].

    def transform(self, node):
        # TODO
        return node

