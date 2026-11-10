"""Version 3.2: tableau-compatible unbolded order, then contractions.

No four-label-specific weights. This module is installed only in an isolated
process using the frozen arithmetic snapshot alongside it.
"""
from functools import lru_cache

STRUCTURAL_KEY = None


@lru_cache(maxsize=50000)
def unbolded(mon):
    edges = []
    for _, _, labels, colors in mon:
        for j, color in enumerate(colors):
            i, k = sorted((labels[j], labels[(j+1) % len(labels)]))
            edges.append((color, i, k) if color else (color, -i, -k))
    return tuple(sorted(edges))


@lru_cache(maxsize=50000)
def key(mon):
    old = STRUCTURAL_KEY(mon)
    # At equal total degree, ascending factor-list lex is the negative
    # exponent comparison from the smallest bracket variable upwards.
    return old[0], unbolded(mon), old[1:]


def install(b):
    global STRUCTURAL_KEY
    if STRUCTURAL_KEY is None:
        STRUCTURAL_KEY = b.mkey
    key.cache_clear()
    unbolded.cache_clear()
    STRUCTURAL_KEY.cache_clear()
    b.mkey = key


def top_behavior(row):
    if not row:
        return 'zero'
    d = max(sum(u[0] for u in mon) for mon in row)
    top = [mon for mon in row if sum(u[0] for u in mon) == d]
    if len(top) == 1:
        return 'degree_lowering'
    return ('preserves_unbolded' if len({unbolded(mon) for mon in top}) == 1
            else 'changes_unbolded')


def tableau_status(mon, n):
    angles, squares = [], []
    for color, i, j in unbolded(mon):
        if color:
            angles.append((i, j))
        else:
            i, j = -i, -j
            squares.append(tuple(k for k in range(1, n+1) if k not in (i,j)))
    angles.sort(); squares.sort()
    def standard(columns):
        return all(all(x <= y for x,y in zip(a,z))
                   for a,z in zip(columns, columns[1:]))
    return {'separate_chiral_SSYT': standard(angles) and standard(squares),
            'combined_massless_SSYT': standard(squares+angles) if n >= 4 else None}
