# This is a part of Esotope Brainfuck-to-C Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *
from bfc.codegen.c import *

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

class Transformer(object):
    def __init__(self, target):
        assert isinstance(target, list)
        self.target = target
        self.cursormin = 0
        self.cursormax = 0

    def __iter__(self):
        return self

    def next(self):
        if self.cursormax >= len(self.target):
            raise StopIteration
        self.cursormin = self.cursormax
        self.cursormax += 1
        return self.cursormin, self.target[self.cursormin]

    def prepend(self, *items):
        self.target[self.cursormin:self.cursormin] = items
        self.cursormax += len(items)

    def append(self, *items):
        self.target[self.cursormax:self.cursormax] = items
        self.cursormax += len(items)

    def replace(self, *items):
        self.target[self.cursormin:self.cursormax] = items
        nitems = len(items)
        self.cursormax = self.cursormin + nitems

    def truncate(self):
        del self.target[self.cursormax:]

class Compiler(object):
    def __init__(self, cellsize=8):
        self.cellsize = cellsize

    def parse(self, fp):
        nodestack = [Program()]

        def flush(parent, changes, offset):
            for k, v in changes.items():
                if v != 0: parent.append(AdjustMemory(k, v))
            if offset != 0: parent.append(MovePointer(offset))

        changes = {}
        offset = 0
        for lineno, line in enumerate(fp):
            for ch in line:
                if ch == '+':
                    changes[offset] = changes.get(offset, 0) + 1
                elif ch == '-':
                    changes[offset] = changes.get(offset, 0) - 1
                elif ch == '>':
                    offset += 1
                elif ch == '<':
                    offset -= 1
                elif ch in '.,[]':
                    flush(nodestack[-1], changes, offset)
                    changes = {}
                    offset = 0

                    if ch == '.':
                        nodestack[-1].append(Output(Expr[0]))
                    elif ch == ',':
                        nodestack[-1].append(Input(0))
                    elif ch == '[':
                        nodestack.append(While())
                    else:
                        if len(nodestack) < 2:
                            raise ValueError('Not matching ] at line %d' % (lineno+1))
                        loop = nodestack.pop()
                        nodestack[-1].append(loop)

        flush(nodestack[-1], changes, offset)
        if len(nodestack) != 1:
            raise ValueError('Premature end of the loop')
        return nodestack[0]

    def optimize(self, node):
        node = self.optimize_simpleloop_recur(node)
        node = self.optimize_initialmemory(node)
        node = self.optimize_propagate_recur(node)
        node = self.optimize_simpleloop_recur(node)
        node = self.optimize_propagate_recur(node)
        node = self.optimize_removedead_recur(node)
        node = self.optimize_stdlib_recur(node)
        return node

    # calls given function with all nodes within node recursively,
    # in the reverse order of depth-first search.
    def visit(self, node, func):
        visit = self.visit
        for inode in node:
            if isinstance(inode, ComplexNode): visit(inode, func)
        return func(node)

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
    def cleanup(self, node):
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

    # adds redundant SetMemory nodes for later passes. other passes don't know
    # about initial memory contents, so it has to add such information explicitly.
    def optimize_initialmemory(self, node):
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

    # tries to convert various loops into more specific form:
    # - While[p[x]!=v; ...] with offsets=0, which adjusts cell 0 by const amount.
    #   this node will be replaced by Repeat[numrepeat; ...]
    # - While[p[x]!=v; ...] with offsets=0, which sets cell 0 to zero.
    #   this node will be replaced by If[p[x]!=v; ...].
    # - While[p[0]!=v; MovePointer[y]], where y is const.
    #   this nodes will be replaced by SeekMemory[p[y*k]!=v].
    def optimize_simpleloop(self, node):
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

        return self.cleanup(node)

    def optimize_simpleloop_recur(self, node):
        return self.visit(node, self.optimize_simpleloop)

    # extensive loop optimization. it calculates repeat count if possible and
    # tries to convert them into For[].
    def optimize_moreloop(self, node):
        return node

    # propagates cell references and constants as much as possible.
    # requires minptrloops pass for optimal processing. otherwise MovePointer
    # will act as memory blocker.
    def optimize_propagate(self, node):
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
                else:
                    try: del substs[offset]
                    except: pass
            elif isinstance(cur, AdjustMemory):
                alters = mergable = True
                offset = cur.offset
                if offset in substs:
                    substs[offset] += cur.delta
                    if substs[offset].simple():
                        # replace with equivalent SetMemory node.
                        cur = SetMemory(offset, substs[offset])
                        tr.replace(cur)
                    else:
                        del substs[offset]
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
                            if isinstance(cur, AdjustMemory):
                                if isinstance(node[target], SetMemory):
                                    node[target].value += cur.delta
                                else:
                                    node[target].delta += cur.delta
                                if not node[target]:
                                    node[target] = Nop()
                            else:
                                node[target] = cur
                            tr.replace()
                            merged = True

                    if not merged:
                        backrefs[offset] = i

            if not merged:
                target = i
            for ioffset in refs:
                usedrefs[ioffset] = target

        return self.cleanup(node)

    def optimize_propagate_recur(self, node):
        return self.visit(node, self.optimize_propagate)

    # XXX proper name
    def optimize_convarray(self, node):
        return node

    # dead code elimination, sorta. doesn't do so across basic blocks yet.
    def optimize_removedead(self, node):
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

        return self.cleanup(node)

    def optimize_removedead_recur(self, node):
        return self.visit(node, self.optimize_removedead)

    # converts common idioms to direct C library call.
    # - merges Output[] nodes into OutputConst[] node as much as possible.
    def optimize_stdlib(self, node):
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

    def optimize_stdlib_recur(self, node):
        return self.visit(node, self.optimize_stdlib)

    def emit(self, node, debugging=False):
        emitter = Emitter(self, debugging)
        node.emit(emitter)
        return emitter.flush()

