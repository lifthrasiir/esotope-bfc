# This is a part of Esotope Brainfuck Compiler.

class gentype(type):
    def __new__(self, name, bases, dict):
        if '__slots__' not in dict:
            dict['__slots__'] = ()
        if '__gen__' in dict:
            dict['__gen__'] = staticmethod(dict['__gen__'])
        return type.__new__(self, name, bases, dict)

    def __call__(self, *args, **kwargs):
        obj = self.__gen__(self, *args, **kwargs)
        if obj is NotImplemented:
            obj = type.__call__(self, *args, **kwargs)
        return obj

class genobject(object):
    __metaclass__ = gentype
    __gen__ = type.__call__

