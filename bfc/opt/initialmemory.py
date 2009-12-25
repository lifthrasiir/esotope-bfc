# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt.base import BaseOptimizerPass, Transformer

class OptimizerPass(BaseOptimizerPass):
    # adds redundant SetMemory nodes for later passes. other passes don't know
    # about initial memory contents, so it has to add such information explicitly.

    def transform(self, node):
        if not isinstance(node, Program):
            return node

        offsets = 0
        changed = set([None]) # for getting rid of None
        tr = Transformer(node)
        for i, cur in tr:
            refs = cur.prereferences().movepointer(offsets)
            updates = cur.preupdates().movepointer(offsets)

            zerorefs = set(refs.unsure) - changed
            if zerorefs:
                tr.prepend(*[SetMemory(j - offsets, 0) for j in zerorefs])
                changed.update(zerorefs)
            changed.update(updates.unsure)

            ioffsets = cur.offsets()
            if ioffsets is None: break
            offsets += ioffsets

        return node

