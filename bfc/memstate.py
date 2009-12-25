# This is a part of Esotope Brainfuck Compiler.

from bfc.expr import *
from bfc.nodes import *

class _IntegerSet(object):
    """An internal class for mapping arbitrary integer to object (or None).
    It also accepts finite & infinite slice (i.e. range) as a key."""

    def __init__(self):
        self.modulomap = {} # modulo: list of {quotient: value} on all remainders

    def __setitem__(self, key, value):
        if key is Ellipsis: # applies to every keys
            self.clear()
            key = slice(None, None, None)

        if isinstance(key, slice):
            assert NotImplementedError
        else:
            self.modulomap.setdefault(1, [{}])[0].append(key)

    def __getitem__(self, key):
        try:
            return self.modulomap[1][0][key]
        except:
            raise # XXX

class MemoryState(object):
    """Describes the knowledge about current memory.

    XXX current docstring doesn't reflect current implementation. Ignore it.

    Specifcially, it holds:
    - When the certain memory cell has been (or might have been) updated;
    - When the certain memory cell has been (or might have been) used;
    - The relation of two given memory cells, and;
    - Same as above, but for the certain memory range.

    The "relation" is given as the value of one memory cell in terms of other
    cell, and may be undefined (i.e. None) if it might cause infinite recursion
    or result in non-function such as {0}*{0}+{1}*{1}=4.

    The "range" is a triple of {start:end:step} where end offset is exclusive
    just like Python. In fact, every single memory cell {offset} is a shortcut
    of range {offset:offset+1:1}. Both start and end can be None, and assumed
    to be minus or plus infinity respectively. (In the internal it is guaranteed
    that (end - start) % step == 0, if both start and end is not None.
    External API doesn't have such limitation.)
    """

    def __init__(self, memory=None):
        self.memory = {}
        self.backrefs = {}
        # invariant: if i in memory[j].references(), then j in backrefs[i] and
        #            memory[i] doesn't exist (i.e. "fully flattened out")

        if memory:
            for k, v in dict(memory).items(): self.set(k, v)

    def __replace(self, memory, backrefs, offset, expr):
        if offset in backrefs:
            # replace all affected exprs in memory.
            map = {offset: expr}
            for affected in backrefs[offset]:
                memory[affected] = memory[affected].withmemory(map)

            # updates the back references map by removing original {offset}
            # and adding all references in expr instead.
            refs = expr.references()
            for ref in refs:
                backrefs.setdefault(ref, set()).update(backrefs[offset])
            if offset not in refs: del backrefs[offset]

    def __inverse(self, offset, expr):
        if isinstance(expr, ReferenceExpr):
            # f(x) = x  <->  f~(x) = x
            # if f(x) = y (no {x} present in f(x)), it's not invertible.
            if expr.offset != offset: return None
            return expr

        if isinstance(expr, LinearExpr):
            # f(x) = a * g(x) + b  <->  f~(x) = g~((x - b) / a)
            # g(x) must present exactly once in f(x).
            vary = []
            const = expr[0]
            for coeff, term in expr[1:]:
                if offset in term.references():
                    vary.append((coeff, term))
                else:
                    const += coeff * term
            if len(vary) != 1: return None
            inv = self.__inverse(offset, vary[0][1])
            if inv is None: return None
            return inv.withmemory({offset: (Expr[offset] - const) / vary[0][0]})

        if isinstance(expr, MultiplyExpr):
            # f(x) = g(x) * y  <->  f~(x) = g~(x / y)
            vary = []
            const = Expr(1)
            for factor in expr:
                if offset in factor.references():
                    vary.append(factor)
                else:
                    const *= factor
            if len(vary) != 1: return None
            inv = self.__inverse(offset, vary[0])
            if inv is None: return None
            return inv.withmemory({offset: Expr[offset] / const})

        if isinstance(expr, ExactDivisionExpr):
            # f(x) = g(x) / y  <->  f~(x) = g~(x * y)
            # f(x) = y / g(x)  <->  f~(x) = g~(y / x)
            lhs = expr.lhs
            rhs = expr.rhs
            if offset in lhs.references():
                if offset in rhs.references(): return None
                inv = self.__inverse(offset, lhs)
                if inv is None: return None
                return inv.withmemory({offset: Expr[offset] * rhs})
            else:
                if offset not in rhs.references(): return None
                inv = self.__inverse(offset, rhs)
                if inv is None: return None
                return inv.withmemory({offset: lhs / Expr[offset]})

        return None

    def set(self, offset, expr):
        if not Expr(offset).simple(): # XXX ignore for now
            flushed = self.flush()
            flushed.append(SetMemory(offset, expr))
            return flushed

        offset = int(offset)
        flushed = []
        memory = self.memory
        backrefs = self.backrefs

        expr = expr.withmemory(memory)

        if offset in expr.references():
            assert offset not in memory # invariant

            invexpr = self.__inverse(offset, expr)
            if invexpr is not None:
                # expr references itself but invertible. we can substitute all
                # references of {offset} in memory with inverted expr safely.
                self.__replace(memory, backrefs, offset, invexpr)
            else:
                # all references to expr in memory is invalid, so have to be flushed.
                for affected in backrefs[offset]:
                    flushed.append(SetMemory(affected, memory[affected]))
                    del memory[affected]
                del backrefs[offset]

            flushed.append(SetMemory(offset, expr))

        else:
            # if the offset have been referenced by other cells, substitute all
            # reference to the offset with expanded expr.
            self.__replace(memory, backrefs, offset, expr)

            # add the entry with invariant preserved, if possible.
            memory[offset] = expr
            for ref in expr.references():
                backrefs.setdefault(ref, set()).add(offset)

        return flushed

    def get(self, expr):
        expr = Expr(expr).withmemory(self.memory)
        return [], expr

    def remove(self, offset):
        if not Expr(offset).simple(): # XXX ignore for now
            flushed = self.flush()
            return flushed, offset

        # normally we can keep assignments from flushed.
        return [], offset

    def nodes(self):
        nodes = []
        for offset, value in self.memory.items():
            nodes.append(SetMemory(offset, value))
        return nodes

    def clear(self):
        self.memory.clear()
        self.backrefs.clear()

    def flush(self):
        flushed = self.nodes()
        self.clear()
        return flushed

    def __repr__(self):
        return '<MemoryState: %s>' % ', '.join('%r=%s' % (k, v.compactrepr())
                                               for k, v in self.memory.items())

