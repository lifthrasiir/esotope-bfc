# This is a part of Esotope Brainfuck-to-C Compiler.

# tries to convert various loops into more specific form:
# - While[p[x]!=v; ...] with offsets=0, which adjusts cell 0 by const amount.
#   this node will be replaced by Repeat[numrepeat; ...]
# - While[p[x]!=v; ...] with offsets=0, which sets cell 0 to zero.
#   this node will be replaced by If[p[x]!=v; ...].
# - While[p[0]!=v; MovePointer[y]], where y is const.
#   this nodes will be replaced by SeekMemory[p[y*k]!=v].

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *

from bfc.opt import OptimizerPass, Transformer
from bfc.opt.cleanup import cleanup

def _gcdex(x, y):
    a = 0; b = 1
    c = 1; d = 0
    while x:
        q = y / x; r = y % x
        u = a - c * q; v = b - d * q
        y = x; x = r
        a = c; b = d
        c = u; d = v
    return (a, b, y)

class SimpleLoopPass(OptimizerPass):
    def _transform(self, node):
        overflow = 1 << self.cellsize

        tr = Transformer(node)
        for i, cur in tr:
            if not isinstance(cur, While): continue
            if not isinstance(cur.cond, MemNotEqual): continue

            target = cur.cond.target
            value = cur.cond.value

            if target == 0 and len(cur) == 1 and isinstance(cur[0], MovePointer):
                tr.replace(SeekMemory(0, cur[0].offset, value))
                continue

            if cur.offsets() != 0: continue

            flag = True # whether Repeat[] is applicable
            cell = Expr()
            mode = 0 # 0:adjust, 1:set, -1:unknown

            for inode in cur:
                if isinstance(inode, AdjustMemory):
                    if inode.offset == target:
                        cell += inode.delta
                elif isinstance(inode, SetMemory):
                    if inode.offset == target:
                        cell = inode.value
                        mode = 1
                else:
                    if not inode.pure():
                        flag = False
                    if inode.offsets() != 0:
                        flag = False
                        mode = -1

                    updates = inode.postupdates().unsure
                    if None in updates or target in updates:
                        flag = False
                        mode = -1

                refs = inode.postreferences().unsure - inode.postupdates().sure
                if None in refs or target in refs:
                    flag = False # references target, cannot use Repeat[]

            if mode < 0 or not cell.simple(): continue
            delta = (value - int(cell)) % overflow

            if mode > 0:
                if delta == 0:
                    # XXX SetMemory is added temporarily; we should implement
                    # SSA-based optimizer and it will recognize them across basic blocks
                    tr.replace(If(cur.cond, cur[:]), SetMemory(target, value))
                else:
                    infloop = While(Always())
                    if not cur.pure(): # e.g. +[.[-]+]
                        infloop.extend(cur)
                    tr.replace(infloop)

            elif flag:
                # let w be the overflow value, which is 256 for char etc.
                # then there are three cases in the following code:
                #     i = 0; for (j = 0; i != x; ++j) i += m;
                #
                # 1. if m = 0, it loops forever.
                # 2. otherwise, the condition j * m = x (mod w) must hold.
                #    let u * m + v * w = gcd(m,w), and
                #    1) if x is not a multiple of gcd(m,w), it loops forever.
                #    2) otherwise it terminates and j = u * (x / gcd(m,w)).
                #
                # we can calculate u and gcd(m,w) in the compile time, but
                # x is not (yet). so we shall add simple check for now.

                if delta == 0:
                    tr.replace(While(Always()))
                    continue

                u, v, gcd = _gcdex(delta, overflow)
                diff = Expr[target] - value
                count = (u % overflow) * (diff // gcd)

                inodes = [inode for inode in cur
                          if not (isinstance(inode, (SetMemory, AdjustMemory)) and
                                  inode.offset == target)]

                result = []
                if gcd > 1: 
                    # no need to check if x is a multiple of gcd(m,w) (=1).
                    result.append(If(ExprNotEqual(diff % gcd, 0),
                                     [While(Always())]))
                if inodes:
                    # don't emit Repeat[] if [-] or [+] is given.
                    result.append(Repeat(count, inodes))
                result.append(SetMemory(target, value))
                tr.replace(*result)

        return cleanup(node)

    def transform(self, node):
        return self.visit(node, self._transform)

