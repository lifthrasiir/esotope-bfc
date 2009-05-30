# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt.base import BaseOptimizerPass, Transformer
from bfc.opt.cleanup import cleanup

class OptimizerPass(BaseOptimizerPass):
    # dead code elimination, sorta. doesn't do so across basic blocks yet.

    def _transform(self, node):
        unusedcells = {} # cell -> node which last updated this cell
        unusednodes = set()
        unusedmoves = []

        offsets = 0
        tr = Transformer(node)
        for i, cur in tr:
            ioffsets = cur.offsets()
            if ioffsets is None:
                unusedcells.clear()
                unusednodes.clear()
            else:
                offsets += ioffsets

            pure = cur.pure() and cur.returns()
            if pure: # to remove non-I/O nodes independent to memory cells
                unusedmoves.append(i)

            irefs = cur.postreferences().unsure
            iupdates = cur.postupdates().sure
            removable = pure and ioffsets == 0
            if irefs or iupdates:
                # any pointer moves before this cell cannot be removed
                del unusedmoves[:]

            # delete references to all nodes which updates the cell which
            # this node can reference, thus cannot be removed.
            if None in irefs:
                unusedcells.clear()
                unusednodes.clear()
            else:
                for j in irefs:
                    j += offsets
                    try: unusednodes.discard(unusedcells.pop(j))
                    except: pass

            # now removes all nodes which cell updates have been never
            # referenced, and is to be (certainly) updated by this node.
            iupdates.discard(None)
            for j in iupdates:
                j += offsets
                try:
                    oldi = unusedcells[j]
                    unusednodes.remove(oldi) # will raise exception if none
                    node[oldi] = Nop()
                except:
                    pass

                if removable:
                    unusedcells[j] = i
                    unusednodes.add(i)

        if isinstance(node, Program):
            for i in unusednodes:
                node[i] = Nop()
            for i in unusedmoves:
                node[i] = Nop()

        return cleanup(node)

    def transform(self, node):
        return self.visit(node, self._transform)

