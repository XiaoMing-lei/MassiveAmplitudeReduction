"""Dimension-correct mass content normalization for catalogs with n > 4.

The inherited arithmetic routine used range(4) to strip a common mass
monomial. For five-point coefficients this truncated the last exponent,
even when the common power was zero. Everything else is unchanged.
Opt-in installation leaves old archives and running workers untouched.
"""
from math import gcd
import construct_route_pool as construction

b = construction.b


def primitive(row):
    if not row:
        return row, b.ONE
    entries = [(e, v) for co in row.values() for e, v in co.items()]
    width = len(b.ZERO)
    assert all(len(e) == width for e, _ in entries), 'Mixed/truncated mass exponent lengths'
    content = 0
    for _, value in entries:
        content = gcd(content, value)
    common = tuple(min(e[i] for e, _ in entries) for i in range(width))
    pivot = row[max(row, key=b.mkey)]
    if pivot[max(pivot)] < 0:
        content = -content
    if content == 1 and common == b.ZERO:
        return row, b.ONE
    result = {mon: {tuple(a-z for a, z in zip(e, common)): value//content
                    for e, value in co.items()} for mon, co in row.items()}
    return result, {common: content}


def install():
    b.primitive = primitive

