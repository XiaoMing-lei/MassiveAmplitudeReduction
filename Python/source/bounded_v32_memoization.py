"""Bound pure-function memoizers, including aliases retained by v3.2 modules.

The earlier installer inspected only arithmetic_snapshot. In particular,
ssyt_order.STRUCTURAL_KEY still pointed at the original unbounded wrapper.
Replace aliases by function identity across this complete source tree.
Only pure memoization changes; the wrapped functions and return values do not.
"""
from functools import lru_cache
from pathlib import Path
import sys


def source_modules():
    root=Path(__file__).resolve().parent
    for module in tuple(sys.modules.values()):
        filename=getattr(module,'__file__',None)
        if not filename:continue
        try:Path(filename).resolve().relative_to(root)
        except ValueError:continue
        yield module


def bound_function_caches():
    replacements={};changed=[]
    for module in source_modules():
        for name,value in tuple(vars(module).items()):
            if not hasattr(value,'cache_info') or not hasattr(value,'__wrapped__'):continue
            if value.cache_info().maxsize is not None:continue
            if id(value) not in replacements:
                limit=2000 if value.__name__=='external_children' else 50000
                replacements[id(value)]=lru_cache(maxsize=limit)(value.__wrapped__)
            setattr(module,name,replacements[id(value)])
            changed.append(module.__name__+'.'+name)
    return changed


def cache_inventory():
    result={};seen=set()
    for module in source_modules():
        for name,value in tuple(vars(module).items()):
            if not hasattr(value,'cache_info') or id(value) in seen:continue
            seen.add(id(value));result[module.__name__+'.'+name]=value.cache_info()._asdict()
    return result
