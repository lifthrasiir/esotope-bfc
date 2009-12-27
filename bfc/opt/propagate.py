# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt.base import BaseOptimizerPass, Transformer
from bfc.opt.cleanup import cleanup

class OptimizerPass(BaseOptimizerPass):
    # propagates cell references and constants as much as possible.
    # requires minptrloops pass for optimal processing. otherwise MovePointer
    # will act as memory blocker.

    def _transform(self, node):
        backrefs = {}
        usedrefs = {}
        substs = {} # only for simple one, unless some vars are not current

        tr = Transformer(node)
        for i, cur in tr:
            cur.withmemory(substs)

            alters = mergable = False
            offset = None
            refs = []
            if isinstance(cur, Nop):
                pass
            elif isinstance(cur, SetMemory):
                alters = mergable = True
                offset = cur.offset
                if cur.value.simple():
                    substs[offset] = cur.value
                elif cur.delta.simple():
                    if offset in substs:
                        substs[offset] += cur.delta
                        if substs[offset].simple():
                            # replace with equivalent SetMemory node.
                            cur = SetMemory(offset, substs[offset])
                            tr.replace(cur)
                        else:
                            del substs[offset]
                else:
                    try: del substs[offset]
                    except: pass
            elif isinstance(cur, Input):
                alters = True
                offset = cur.offset
                try: del substs[offset]
                except: pass
            elif isinstance(cur, Output):
                pass
            else: # MovePointer, While etc.
                backrefs.clear()
                usedrefs.clear()
                substs.clear()
                if isinstance(cur, (While, If)) and isinstance(cur.cond, MemNotEqual):
                    substs[cur.cond.target] = cur.cond.value
                elif isinstance(cur, SeekMemory):
                    substs[cur.target] = cur.value

            refs = cur.postreferences().unsure
            merged = False
            if alters:
                if not mergable:
                    # prohibit next merging attempt.
                    try: del backrefs[offset]
                    except: pass
                else:
                    # we can merge node[target] and node[i] if:
                    # - no operation has changed cell k between them. (thus such target
                    #   is backrefs[offset], as it is updated after change)
                    # - no operation has referenced the target cell between them.
                    #   node[target] itself could reference that cell.
                    # - no operation has changed cell(s) referenced by value.
                    #   similar to above, node[target] is excluded from this rule.
                    if offset in backrefs:
                        target = backrefs[offset]
                        if target >= usedrefs.get(offset, -1) and \
                                all(target >= backrefs.get(ioffset, -1) for ioffset in refs):
                            assume = {offset: node[target].value}
                            node[target].value = cur.value.withmemory(assume)
                            tr.replace()
                            merged = True

                    if not merged:
                        backrefs[offset] = i

            if not merged:
                target = i
            for ioffset in refs:
                usedrefs[ioffset] = target

        return cleanup(node)

    def transform(self, node):
        return self.visit(node, self._transform)

