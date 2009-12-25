# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *
from bfc.memstate import *

from bfc.opt.base import BaseOptimizerPass, Transformer
from bfc.opt.cleanup import cleanup

class OptimizerPass(BaseOptimizerPass):
    # propagates cell references and constants as much as possible.
    # requires minptrloops pass for optimal processing. otherwise MovePointer
    # will act as memory blocker.

    def _transform(self, node):
        state = MemoryState()
        substs = {} # special casing for self-recursion; applied before memstate

        result = []
        for cur in node:
            if isinstance(cur, Nop):
                pass
            elif isinstance(cur, SetMemory):
                result += state.set(cur.offset, cur.value)
            elif isinstance(cur, Input):
                flushed, offset = state.remove(cur.offset)
                result += flushed
                result.append(Input(offset))
            elif isinstance(cur, Output):
                flushed, expr = state.get(cur.expr)
                assert not flushed
                result.append(Output(expr))
            else: # MovePointer, While etc.
                for offset, value in substs.items():
                    result.append(SetMemory(offset, value))
                result += state.flush()
                if isinstance(cur, ComplexNode):
                    cur = self._transform(cur)
                result.append(cur)

        for offset, value in substs.items():
            result.append(SetMemory(offset, value))
        result += state.flush()
        print node
        node[:] = result
        print node
        return cleanup(node)

    def transform(self, node):
        return self._transform(node)

