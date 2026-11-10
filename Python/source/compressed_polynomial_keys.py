"""Exact compact identity keys; preserve hashes and decoded set iteration.

These keys are only identifiers, never monomials used for mathematical order.
The degree and insertion ticket remain the S-queue priorities.
"""
from collections import defaultdict
from collections.abc import MutableSet
import marshal
import zlib


class Key:
    __slots__=('data','hashed')

    def __init__(self,value):
        if isinstance(value,Key):
            self.data,self.hashed=value.data,value.hashed
        else:
            self.data=zlib.compress(marshal.dumps(value,2),1)
            self.hashed=hash(value)

    def unpack(self):return marshal.loads(zlib.decompress(self.data))
    def __hash__(self):return self.hashed

    def __eq__(self,other):
        if isinstance(other,Key):return self.data==other.data
        return self.unpack()==other

    def __reduce__(self):return restore_key,(self.data,)


def restore_key(data):
    value=Key.__new__(Key);value.data=data;value.hashed=hash(value.unpack())
    return value


def pack(value):return value if isinstance(value,Key) else Key(value)
def unpack(value):return value.unpack() if isinstance(value,Key) else value


class EncodedSet(MutableSet):
    def __init__(self,values=()):self.entries={pack(value) for value in values}
    def __len__(self):return len(self.entries)
    def __iter__(self):return (value.unpack() for value in self.entries)
    def __contains__(self,value):return pack(value) in self.entries
    def add(self,value):self.entries.add(pack(value))
    def discard(self,value):self.entries.discard(pack(value))
    def clear(self):self.entries.clear()
    def __bool__(self):return bool(self.entries)


class EncodingIndex(defaultdict):
    def __init__(self,values=()):
        super().__init__(EncodedSet)
        for key,value in (values.items() if hasattr(values,'items') else values):
            self[key]=value if isinstance(value,EncodedSet) else EncodedSet(value)

    def __reduce__(self):return EncodingIndex,(dict(self),)
