# This is a part of Esotope Brainfuck Compiler.

import re as _re

from py.test import raises

_STRING_PATTERN = _re.compile(r'''('(?:\\(?:x[0-9a-f]{2}|[0-7]{1,3}|.)|.)*' |
                                   "(?:\\(?:x[0-9a-f]{2}|[0-7]{1,3}|.)|.)*")''',
                              _re.I | _re.X)
def remove_spaces(s):
    '''Strips every whitespaces in s, except those in the quoted string. The format
    for string is same to Python repr.'''
    tokens = _STRING_PATTERN.split(s)
    tokens[0::2] = [t.replace(' ','').replace('\t','').replace('\n','').replace('\r','')
                    for t in tokens[0::2]]
    return ''.join(tokens)

def eq(node, str):
    '''Returns True if representation of node matches str except whitespaces.'''
    return remove_spaces(repr(node)) == remove_spaces(str)

