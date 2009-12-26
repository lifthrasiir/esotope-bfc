# This is a part of Esotope Brainfuck Compiler.

from bfc.nodes import *
from bfc.expr import *
from bfc.cond import *
from bfc.memstate import *

from bfc.opt.base import BaseOptimizerPass, Transformer
from bfc.opt.cleanup import cleanup

class OptimizerPass(BaseOptimizerPass):
    # specialized loop optimization, including:
    # - transforms deeply-nested If[...,If[...]] constructs into single If[...]
    #   if possible.

    def __search_singleif(self, node):
        ifpos = None
        for i, inode in enumerate(node):
            if isinstance(inode, If):
                if ifpos is not None: return None # multiple loops
                ifpos = i
            elif not isinstance(inode, SetMemory):
                return None
        return ifpos

    def __propagate_mini(self, nodes):
        subst = {}
        result = []
        for cur in nodes:
            if not cur: continue
            assert isinstance(cur, SetMemory)
            if cur.value.references().difference([cur.offset]): # flush mappings
                result.extend(SetMemory(k,v) for k,v in subst.items() if v != Expr[k])
                result.append(cur)
            else:
                subst[cur.offset] = cur.value.withmemory(subst)
        result.extend(SetMemory(k,v) for k,v in subst.items() if v != Expr[k])
        return result

    def _transform(self, node):
        ifpos = self.__search_singleif(node)
        if ifpos is None: return node
        ifnode = node[ifpos]
        if not ifnode.pure() or ifnode.offsets() != 0: return node

        statemap = {}
        invmap = {}
        for inode in node[:ifpos]:
            refs = inode.value.references()
            if refs and refs != set([inode.offset]): return node
            statemap[int(inode.offset)] = inode.value.withmemory(statemap)
        for k, v in statemap.items():
            invv = v.inverse(k)
            if invv is None: return node # should be invertible
            invmap[k] = invv
        prealters = set(statemap.keys())

        if any(i.postreferences() for i in node[ifpos+1:]): return None
        bodyupdates = reduce(set.union, [i.postupdates().unsure for i in ifnode], set())
        postupdates = reduce(set.union, [i.postupdates().unsure for i in node[ifpos+1:]], set())
        if not (prealters & bodyupdates) <= postupdates: return node

        if len(ifnode) > 1 and isinstance(ifnode[0], If) and \
                all(isinstance(i, SetMemory) for i in ifnode[0]) and \
                all(isinstance(i, SetMemory) for i in ifnode[1:]):
            # f() If[c; If[d; g()] h()] i() -> If[c/f; If[d/f; g'/f()] h'/f()] f() i()
            # where g' and h' are pre-propagated node lists against h() and i().
            if any(i.postreferences() for i in ifnode[1:]): return None
            ibodyupdates = reduce(set.union, [i.postupdates().unsure for i in ifnode[0]], set())
            ipostupdates = reduce(set.union, [i.postupdates().unsure for i in ifnode[1:]], set())
            if not (prealters & ibodyupdates) <= ipostupdates: return node

            ifcond = ifnode.cond.withmemory(statemap)
            iifcond = ifnode[0].cond.withmemory(statemap)
            iifbody = []
            lastdefs = {}
            for i, inode in enumerate(ifnode[0]):
                offset = Expr(inode.offset)
                value = inode.value
                iifbody.append(SetMemory(offset, value.withmemory(statemap)))
                for ref in inode.postreferences().unsure:
                    if ref in lastdefs: del lastdefs[ref]
                for offset in inode.postupdates().unsure:
                    if offset in statemap: del statemap[offset]
                    lastdefs[offset] = i
            for k, v in lastdefs.items(): # clears out the duplicated references in body
                if k in ipostupdates or k in postupdates: iifbody[v] = Nop()

            ifbody = [If(iifcond, self.__propagate_mini(iifbody))]
            lastdefs = {}
            for i, inode in enumerate(ifnode):
                if i == 0: continue # If node
                offset = Expr(inode.offset)
                value = inode.value
                ifbody.append(SetMemory(offset, value.withmemory(statemap)))
                for ref in inode.postreferences().unsure:
                    if ref in lastdefs: del lastdefs[ref]
                for offset in inode.postupdates().unsure:
                    if offset in statemap: del statemap[offset]
                    lastdefs[offset] = i
            for k, v in lastdefs.items(): # clears out the duplicated references in body
                if k in postupdates: ifbody[v] = Nop()

            ifnode = If(ifcond, ifbody[:1] + self.__propagate_mini(ifbody[1:]))
            node[:] = [ifnode] + self.__propagate_mini(node[:ifpos] + node[ifpos+1:])
            ifpos = 0

        if len(ifnode) == 1 and isinstance(ifnode[0], If):
            # f() If[c; If[d; g()]] h() -> f() If[c&d; g()] h() -> ...
            ifnode.cond &= ifnode[0].cond
            ifnode[:] = ifnode[0][:]

        if all(isinstance(i, SetMemory) for i in ifnode):
            # f() If[c; g()] h() -> If[c/f; g'/f()] f() h()
            # where g' is a pre-propagated node list against h().
            ifcond = ifnode.cond.withmemory(statemap)
            ifbody = []
            lastdefs = {}
            for i, inode in enumerate(ifnode):
                offset = Expr(inode.offset)
                value = inode.value
                ifbody.append(SetMemory(offset, value.withmemory(statemap)))
                for ref in inode.postreferences().unsure:
                    if ref in lastdefs: del lastdefs[ref]
                for offset in inode.postupdates().unsure:
                    if offset in statemap: del statemap[offset]
                    lastdefs[offset] = i
            for k, v in lastdefs.items(): # clears out the duplicated references in body
                if k in postupdates: ifbody[v] = Nop()

            node[:] = ([If(ifcond, self.__propagate_mini(ifbody))] +
                       self.__propagate_mini(node[:ifpos] + node[ifpos+1:]))

        return node

    def transform(self, node):
        return self.visit(node, self._transform)

