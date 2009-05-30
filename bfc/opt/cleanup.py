# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt.base import Transformer

def cleanup(node):
    # general node cleanup routine. it does the following jobs:
    # - removes every no-op nodes, including If[False; ...] and k+=0.
    # - flattens Repeat[num; ...] node with all memory ops to parent.
    # - flattens If[True; ...] node to parent.
    # - merges MovePointer[] nodes as much as possible, and adjusts
    #   other nodes accordingly.
    # - removes every (dead) nodes after non-returning node.
    #
    # this is not recursive, and intended to be called in the end of other
    # optimization passes.

    offsets = 0
    tr = Transformer(node)
    for i, cur in tr:
        if not cur: # remove no-op
            tr.replace()
            continue

        cur.movepointer(offsets)
        ioffsets = cur.offsets()
        if ioffsets is not None:
            offsets += ioffsets

        if isinstance(cur, MovePointer):
            tr.replace()
            continue

        if isinstance(cur, If):
            if isinstance(cur.cond, Always):
                tr.replace(*cur)

        elif isinstance(cur, Repeat):
            hasset = False
            for inode in cur:
                if isinstance(inode, SetMemory):
                    if not inode.value.simple(): break
                    hasset = True
                elif isinstance(inode, AdjustMemory):
                    if not inode.delta.simple(): break
                else:
                    break

            else:
                for inode in cur:
                    if isinstance(inode, AdjustMemory):
                        inode.delta *= cur.count
                if hasset:
                    # cannot flatten, but we can turn it into If[]
                    tr.replace(If(ExprNotEqual(cur.count, 0), cur[:]))
                else:
                    tr.replace(*cur)

        # if this command doesn't return, ignore all nodes after it.
        if not cur.returns():
            tr.truncate()
            offsets = 0

    if offsets != 0:
        node.append(MovePointer(offsets))

    return node

