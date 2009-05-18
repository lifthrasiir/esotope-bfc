# This is a part of Esotope Brainfuck-to-C Compiler.

# converts common idioms to direct C library call.
# - merges Output[] nodes into OutputConst[] node as much as possible.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt import OptimizerPass, Transformer

class StdlibPass(OptimizerPass):
    def _transform(self, node):
        laststr = []
        tr = Transformer(node)
        for i, cur in tr:
            if isinstance(cur, Output) and cur.expr.simple():
                tr.replace()
                laststr.append(chr(int(cur.expr) & 0xff))
            elif isinstance(cur, OutputConst):
                tr.replace()
                laststr.append(cur.str)
            elif not cur.pure(): # I/O cannot be reordered!
                if laststr:
                    tr.prepend(OutputConst(''.join(laststr)))
                laststr = []

        if laststr:
            node.append(OutputConst(''.join(laststr)))

        return node

    def transform(self, node):
        return self.visit(node, self._transform)

