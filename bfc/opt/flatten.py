# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt.base import BaseOptimizerPass, Transformer

class OptimizerPass(BaseOptimizerPass):
    def _transform(self, node):
        result = []

        changes = {}
        changesabs = {}
        offset = 0
        for cur in node:
            if isinstance(cur, SetMemory):
                ioffset = offset + cur.offset
                if cur.delta.simple():
                    changes[ioffset] = changes.get(ioffset, 0) + cur.delta
                else:
                    changes[ioffset] = cur.value
                    changesabs[ioffset] = True
            elif isinstance(cur, MovePointer):
                offset += cur.offset
            else:
                # flush memory changes, but not pointer change.
                # pointer change is propagated and eliminated as much as possible.
                for k, v in changes.items():
                    if changesabs.get(k):
                        result.append(SetMemory(k, v))
                    elif v != 0:
                        result.append(AdjustMemory(k, v))
                changes.clear()
                changesabs.clear()

                cur.movepointer(offset)
                result.append(cur)

        for k, v in changes.items():
            if changesabs.get(k):
                result.append(SetMemory(k, v))
            elif v != 0:
                result.append(AdjustMemory(k, v))
        if offset != 0:
            result.append(MovePointer(offset))

        node[:] = result
        return node

    def transform(self, node):
        return self.visit(node, self._transform)

