"""Input-driven B': exact tensor replacements and reusable contextual cache.

No component evaluation, basis enumeration, or precomputed descendant table is
used for construction or matching. Existing graph/determinant arithmetic is
reused. A returned reduction is not claimed to be a unique physical normal form.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import gcd
from pathlib import Path
import json
import time
import sys

_local_dependencies=Path(__file__).resolve().parents[1]/'.tensor-rule-deps'
if _local_dependencies.exists():sys.path.insert(0,str(_local_dependencies))
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ

import build_bounded_four_point as b
import construct_parent_descendants as p
from verify_bounded_four_point import freeze

_normalize_unit = b.normalize_unit
_unit_key = b.order.unit_key
_primitive = p.primitive
_pmul = b.pmul
_add_term = b.add_term
N = 4
MASS_RING=None


def pmul(a,c):
    if not a or not c:return {}
    if len(a)==1 and b.ZERO in a:
        factor=a[b.ZERO]
        return {e:factor*v for e,v in c.items()}
    if len(c)==1 and b.ZERO in c:
        factor=c[b.ZERO]
        return {e:factor*v for e,v in a.items()}
    return _pmul(a,c)


def add_term(row,mon,coefficient):
    if not coefficient:return
    if mon not in row:
        row[mon]=dict(coefficient)
        return
    _add_term(row,mon,coefficient)


class FirstAction(Exception):
    def __init__(self, action):
        self.action = action


@lru_cache(maxsize=100000)
def common_mass_polynomial(coefficients):
    if any(len(c)==1 for c in coefficients):
        # Common integer/monomial content has already been removed.
        return b.ONE
    # Strip individual monomial/content factors before polynomial GCD. Old
    # fraction-free records can contain thousands of terms in one common
    # factor, while their primitive tensor coefficients are just masses.
    values=set()
    for c in coefficients:
        powers=tuple(min(e[i] for e,v in c) for i in range(len(b.ZERO)))
        content=0
        for e,v in c:content=gcd(content,v)
        if dict(c)[max(e for e,v in c)]<0:content=-content
        values.add(tuple(sorted((tuple(a-z for a,z in zip(e,powers)),v//content) for e,v in c)))
    values=sorted(values,key=len)
    if len(values)==1:return dict(values[0])
    g=MASS_RING.from_dict(dict(values[0]))
    polys=[MASS_RING.from_dict(dict(c)) for c in values[1:]]
    try:
        for co in polys:co.exquo(g)
        return {e:int(v) for e,v in g.to_dict().items()}
    except Exception:
        pass
    for co in polys:
        g=g.gcd(co)
        if g==MASS_RING.one:return b.ONE
    return {e:int(v) for e,v in g.to_dict().items()}


def polynomial_divide(a,d):
    return {e:int(v) for e,v in MASS_RING.from_dict(a).exquo(MASS_RING.from_dict(d)).to_dict().items()}


def primitive(row):
    row,factor,scale=_primitive(row)
    if row:
        g=common_mass_polynomial(tuple(sorted(tuple(sorted(c.items())) for c in row.values())))
        if g!=b.ONE:
            row={m:polynomial_divide(c,g) for m,c in row.items()}
            scale=b.pmul(scale,g)
    return row,factor,scale


def cancel_denominator(row,den):
    if den==b.ONE or not row:return row,den
    g=MASS_RING.from_dict(den)
    for c in row.values():
        g=g.gcd(MASS_RING.from_dict(c))
        if g==MASS_RING.one:return row,den
    content={e:int(v) for e,v in g.to_dict().items()}
    if content!=b.ONE:
        row={m:polynomial_divide(c,content) for m,c in row.items()}
        den=polynomial_divide(den,content)
    return row,den


@lru_cache(None)
def normalize_unit(kind, labels, colors):
    # Keep a general long alternating trace as a tensor trace, not as a new
    # independent scalar generator. Original M/S replacements still act inside.
    n = len(colors)
    simple = all(labels[j] != labels[(j + 1) % len(labels)] for j in range(n))
    alternating = all(colors[j - 1] != colors[j] for j in range(n)) if kind else True
    if kind and n >= 6 and simple and alternating and not (n == 6 and len(set(labels)) <= 3):
        return {(b.order.trace(labels, colors),): b.ONE}
    return _normalize_unit(kind, labels, colors)


def unit_key(u):
    if not u[1] or u[0] <= 4:
        return _unit_key(u)
    length, kind, labels, colors = u
    edges = []
    for j, color in enumerate(colors):
        pair = tuple(sorted((labels[j], labels[(j + 1) % len(labels)])))
        edges.append((color,) + (pair if color else tuple(-x for x in pair)))
    return length, 0, tuple(sorted(edges)), labels, colors


def configure(n=4, degree=6):
    global N,MASS_RING
    N = n
    b.ZERO = (0,) * max(n, 4)
    b.ONE = {b.ZERO: 1}
    MASS_RING=ring(','.join(f'm{i+1}' for i in range(len(b.ZERO))),ZZ)[0]
    common_mass_polynomial.cache_clear()
    p.primitive=primitive
    def mass(i, power=1, sign=1):
        e = [0] * len(b.ZERO)
        e[i - 1] = power
        return {tuple(e): sign}
    b.mass = mass
    b.pmul = pmul
    b.add_term = add_term
    b.normalize_unit = normalize_unit
    b.order.unit_key = unit_key
    b.ORDER_BOUND = degree
    b.mkey.cache_clear()
    _normalize_unit.cache_clear()
    normalize_unit.cache_clear()
    p.PARTICLES = n


def originals(n):
    p.PARTICLES = n
    for family, labels, raw in p.raw_originals():
        if family == 'S' and max(Counter(labels[1:]).values()) > 2:
            continue
        yield family, labels, freeze(raw)


def poly_scale(row, coefficient):
    if coefficient == b.ONE:
        return dict(row)
    return {m: b.pmul(c, coefficient) for m, c in row.items()}


def monomial_row(m):
    return {m: b.ONE}


@lru_cache(None)
def momentum_leading_label(i, j, n):
    """Prescribed original M_ij head, after same-particle determinants."""
    return next(k for k in range(1, n + 1) if k not in (i, j))


def parent_patterns(parent, unique_momentum_lm=False):
    if parent['raw'] is not None:
        representative_used=False
        repeated_s=(parent['family']=='S' and len(set(parent['labels'][1:]))<4)
        momentum_term=(momentum_leading_label(*parent['labels'], len(parent['raw']))-1
                       if unique_momentum_lm and parent['family']=='M' else None)
        for ti, (sign, ll, bb, ee) in enumerate(parent['raw']):
            if momentum_term is not None and ti != momentum_term:
                continue
            if all(ll[a] != ll[z] for a, z, _ in bb):
                # For (2,1,1) and (2,2) Schouten the two potential terms are
                # related by a same-particle free-slot permutation. All joins
                # of the representative are still enumerated. Distinct-label
                # Schouten terms have different orbits and are all retained.
                if repeated_s and representative_used:continue
                representative_used=True
                yield ti, (ll, bb, ee)
    elif parent['row']:
        d = max(map(p.degree, parent['row']))
        for ti, m in enumerate(sorted(parent['row'], key=b.mkey, reverse=True)):
            if p.degree(m) == d:
                yield ti, b.graph(m)


def graph_details(mon):
    ll, bb, ee = b.graph(mon)
    owners = []
    for ui, u in enumerate(mon):
        owners.extend([ui] * u[0])
    edge_of = {v: i for i, (a, z, c) in enumerate(bb) for v in (a, z)}
    return ll, bb, ee, owners, edge_of


def selected_block(mon, edges):
    ll, bb, ee, owners, edge_of = graph_details(mon)
    touched = {owners[e] for e in edges}
    block = tuple(u for i, u in enumerate(mon) if i in touched)
    rest = tuple(u for i, u in enumerate(mon) if i not in touched)
    old_edges = [i for i in range(len(bb)) if owners[i] in touched]
    renumber = {v: j for j, e in enumerate(old_edges) for v in [e]}
    return block, rest, tuple(renumber[e] for e in edges)


def local_signature(mon, selected_edges):
    # Equal disconnected factors and repeated choices are identified before
    # substitution. Mark the chosen bracket positions inside canonical units.
    chosen = set(selected_edges)
    records = []
    offset = 0
    for u in mon:
        marks = tuple(j for j in range(u[0]) if offset + j in chosen)
        records.append((u, marks))
        offset += u[0]
    return tuple(sorted(records))


def graph_matches(pattern, mon):
    """Injective bracket embeddings preserving all internal contractions."""
    pl, pb, pe = pattern
    ll, bb, ee = b.graph(mon)
    edge_index = defaultdict(list)
    for j, (a, z, c) in enumerate(bb):
        edge_index[(c, tuple(sorted((ll[a], ll[z]))))].append(j)
    possibilities = []
    for a, z, c in pb:
        options = edge_index.get((c, tuple(sorted((pl[a], pl[z])))), ())
        if not options:
            return
        possibilities.append(options)
    sequence = sorted(range(len(pb)), key=lambda i: len(possibilities[i]))
    eadj = {a: z for a, z in ee} | {z: a for a, z in ee}
    used = set()
    mapping = {}
    picked = {}
    seen = set()
    def visit(k):
        if k == len(sequence):
            selection = tuple(sorted(picked.values()))
            sig = (local_signature(mon, selection), tuple(sorted(
                tuple(sorted((mapping[a], mapping[z]))) for a, z in pe)))
            if sig not in seen:
                seen.add(sig)
                yield selection, dict(mapping)
            return
        i = sequence[k]
        a, z, c = pb[i]
        for j in possibilities[i]:
            if j in used:
                continue
            x, y, _ = bb[j]
            if pl[a] != ll[x]:
                x, y = y, x
            mapping[a], mapping[z] = x, y
            if all(v not in mapping or w not in mapping or eadj.get(mapping[v]) == mapping[w]
                   for v, w in pe):
                used.add(j); picked[i] = j
                yield from visit(k + 1)
                used.remove(j); del picked[i]
            del mapping[a]; del mapping[z]
    yield from visit(0)


def embed_physical(row, pattern, mon, selected, mapping):
    """Contract a symmetric physical identity, summing all free-slot choices.

    A specific slot of a symmetrized identity is never arbitrarily selected.
    The common falling-factorial normalization is immaterial for an identity.
    """
    ll, bb, ee = b.graph(mon)
    pl, pb, pe = pattern
    internal = {frozenset((mapping[a], mapping[z])) for a, z in pe}
    remaining_bb = tuple(e for i, e in enumerate(bb) if i not in selected)
    selected_ports = {v for i in selected for v in bb[i][:2]}
    context_ee = tuple(e for e in ee if frozenset(e) not in internal)
    holes = sorted({v for e in context_ee for v in e if v in selected_ports})
    if any(a in selected_ports and z in selected_ports for a, z in context_ee):
        # This contracts two symmetric free indices of the same physical leg.
        return {}
    hole_groups = defaultdict(list)
    for v in holes:
        hole_groups[ll[v]].append(v)
    external = sorted({v for e in remaining_bb for v in e[:2]})
    ext_map = {v: i for i, v in enumerate(external)}
    ext_labels = tuple(ll[v] for v in external)
    ext_brackets = tuple((ext_map[a], ext_map[z], c) for a, z, c in remaining_bb)
    result = {}
    for m, coeff in row.items():
        tl, tb, te = b.graph(m)
        used = {v for e in te for v in e}
        free = defaultdict(list)
        for v, label in enumerate(tl):
            if v not in used:
                free[label].append(v)
        labels = sorted(hole_groups)
        choices = [permutations(free[label], len(hole_groups[label])) for label in labels]
        off = len(ext_labels)
        for assignments in product(*choices):
            sub = dict(ext_map)
            for label, assignment in zip(labels, assignments):
                sub.update((h, off + v) for h, v in zip(hole_groups[label], assignment))
            eps = tuple((off + a, off + z) for a, z in te) + tuple((sub[a], sub[z]) for a, z in context_ee)
            graph = (ext_labels + tl, ext_brackets + tuple((off+a, off+z, c) for a,z,c in tb), eps)
            for out, co in b.normalize_graph(*graph).items():
                b.add_term(result, out, b.pmul(coeff, co))
    return result


class Reducer:
    def __init__(self, n=4, degree=6, unique_momentum_lm=False):
        self.n = n
        self.degree = degree
        self.unique_momentum_lm = unique_momentum_lm
        self.parents = []
        self.original_ids = {}
        self.derived_patterns = []
        self.cache = defaultdict(list)
        self.cache_encodings = defaultdict(set)
        self.action_cache = {}
        self.momentum_cache = {}
        self.original_cache = {}
        self.momentum_polynomial_cache = {}
        self.derived_context_cache = {}
        self.stats = Counter()
        self.version = 0
        self.added_signature = []
        for family, labels, raw in originals(n):
            pid = len(self.parents)
            self.parents.append({'id': pid, 'family': family, 'labels': labels,
                                 'raw': raw, 'row': p.project(raw), 'source': None})
            self.original_ids[(family, tuple(labels))] = pid

    def parent_patterns(self, parent):
        return parent_patterns(parent, self.unique_momentum_lm)

    def matching_derived_patterns(self, mon, input_signature):
        """Optional exact index; the baseline keeps its original ordered scan."""
        return self.derived_patterns

    def embedded_derived_identity(self, parent, ti, pattern, block, edges, port_map):
        """Prepare a complete contextual identity before the actual-LM check."""
        return embed_physical(parent['row'], pattern, block, edges, port_map)

    def add_parent(self, row, source):
        row, factor, scale = p.primitive(row)
        if source and 'removed_scale' in source and (factor or scale!=b.ONE):
            source=dict(source)
            old=source['removed_scale']
            if isinstance(old,list):old={tuple(e):v for e,v in old}
            source['removed_scale']=b.pmul(old,scale)
            source['removed_product']=b.mono(bp_factor(source.get('removed_product',()))+factor)
        key = p.encode(row)
        for rec in self.parents:
            if rec['raw'] is None and p.encode(rec['row']) == key:
                return rec['id'], False
        pid = len(self.parents)
        rec = {'id': pid, 'family': 'S-polynomial', 'labels': None,
               'raw': None, 'row': row, 'source': source}
        self.parents.append(rec)
        for ti, pattern in self.parent_patterns(rec):
            ll,bb,ee=pattern
            signature=Counter((c,tuple(sorted((ll[a],ll[z])))) for a,z,c in bb)
            self.derived_patterns.append((pid, ti, pattern, signature))
        h=max(row,key=b.mkey)
        self.added_signature.append((max(map(p.degree,row)),h))
        self.cache[h].append((row,{'parent':pid,'kind':'derived-product'}))
        self.cache_encodings[h].add(p.encode(row))
        self.version += 1
        # A degree-d physical parent cannot add a contracted replacement to
        # an input of degree <= d. At those degrees it can only act through
        # its untouched product head. Preserve the other matching results;
        # larger inputs are invalidated because new contractions are possible.
        d=max(map(p.degree,row))
        self.action_cache={(self.version,mon,first_only):actions
                           for (_,mon,first_only),actions in self.action_cache.items()
                           if p.degree(mon)<=d and p.quotient(mon,h) is None}
        return pid, True

    def matching_may_have_changed(self, mon, previous_version):
        degree=p.degree(mon)
        return any(degree>d or p.quotient(mon,h) is not None
                   for d,h in self.added_signature[previous_version:])

    def load_cached_descendants(self, records):
        """Load only descendants previously requested and saved by B'."""
        count=0
        for rec in records:
            row,factor,scale=p.primitive(read_row(rec['identity']))
            if not row:continue
            h=max(row,key=b.mkey);encoding=p.encode(row)
            if encoding not in self.cache_encodings[h]:
                source=dict(rec['source'])
                if factor or scale!=b.ONE:
                    source['additional_cache_normalization']={'factor':factor,'scale':scale}
                self.cache[h].append((row,source));self.cache_encodings[h].add(encoding)
                count+=1
        return count

    def original_candidates(self, mon, only_m=False):
        ll, bb, ee, owners, edge_of = graph_details(mon)
        seen = set()
        # Momentums in the input determine the possible original M identities.
        for a, z in ee:
            i, j = edge_of[a], edge_of[z]
            if bb[i][2] == bb[j][2]:
                continue
            sig = ('M', local_signature(mon, (i, j)))
            if sig in seen:
                continue
            seen.add(sig)
            block, rest, edges = selected_block(mon, (i, j))
            bl, br, be = b.graph(block)
            candidates = [e for e in be if {next(t for t,x in enumerate(br) if e[0] in x[:2]),
                                          next(t for t,x in enumerate(br) if e[1] in x[:2])} == set(edges)]
            # For a two-cycle there are two distinct momentum insertions.
            for x, y in candidates:
                # Reject nonleading momentum occurrences before substitution.
                # The contraction placement is retained for the entire identity.
                endpoints = []
                for v in (x, y):
                    aa, zz, color = next(e for e in br if v in e[:2])
                    endpoints.append((color, bl[zz if aa == v else aa]))
                endpoints.sort(reverse=True)
                endpoint_labels = tuple(i for c, i in endpoints)
                leading_momentum = momentum_leading_label(*endpoint_labels, self.n)
                if self.unique_momentum_lm and bl[x] != leading_momentum:
                    self.stats['nonleading_momentum_occurrences_skipped'] += 1
                    continue
                row = {}
                for k in range(1, self.n + 1):
                    labels = list(bl); labels[x] = labels[y] = k
                    for m, co in b.normalize_graph(tuple(labels), br, be).items():
                        b.add_term(row, m, co)
                row, factor, scale = p.primitive(row)
                if not row:
                    continue
                pid = self.original_ids['M', endpoint_labels]
                yield row, rest + factor, {'parent': pid, 'kind': 'M', 'block': block,
                                         'placement': [x, y], 'removed_product': factor,
                                         'matched_momentum': bl[x],
                                         'prescribed_momentum': leading_momentum}
        if only_m:
            return
        for i, j in combinations(range(len(bb)), 2):
            if bb[i][2] != bb[j][2]:
                continue
            labels = sorted(ll[v] for k in (i,j) for v in bb[k][:2])
            if max(Counter(labels).values()) > 2:
                continue
            sig = ('S', local_signature(mon, (i,j)))
            if sig in seen:
                continue
            seen.add(sig)
            block, rest, edges = selected_block(mon, (i,j))
            bl, br, be = b.graph(block)
            a, z, color = br[edges[0]]
            x, y, _ = br[edges[1]]
            row = dict(b.normalize_graph(bl, br, be))
            for replacement, sign in [(((a,x,color),(z,y,color)),-1),
                                      (((a,y,color),(z,x,color)),1)]:
                bs = list(br); bs[edges[0]], bs[edges[1]] = replacement
                for m, co in b.normalize_graph(bl, tuple(bs), be).items():
                    b.add_term(row, m, {e: sign*v for e,v in co.items()})
            row, factor, scale = p.primitive(row)
            if row:
                pid = self.original_ids['S', (color,*labels)]
                yield row, rest + factor, {'parent': pid, 'kind': 'S', 'block': block,
                                         'placement': edges, 'removed_product': factor}

    def momentum_actions(self, mon, all_actions=False):
        key=(mon,all_actions)
        if key not in self.momentum_cache:
            found = []
            seen = set()
            for row, rest, source in self.original_candidates(mon, only_m=True):
                full = p.multiply(row, rest)
                if full and max(full, key=b.mkey) == mon:
                    key = p.encode(full)
                    if key not in seen:
                        seen.add(key); found.append((full, source))
                        if not all_actions:break
            self.momentum_cache[mon,all_actions] = found
        return self.momentum_cache[mon,all_actions]

    def reduce(self, row, only_m=False, reverse=False, trace=False, max_steps=200000,
               excluded_identities=frozenset()):
        pending = dict(row)
        out = {}
        den = b.ONE
        steps = []
        count = 0
        while pending:
            head = max(pending, key=b.mkey)
            actions = (self.momentum_actions(head,all_actions=reverse or bool(excluded_identities))
                       if only_m else self.actions(head, first_only=not reverse and not excluded_identities))
            if excluded_identities:
                # Exclusion is on the primitive identity, including untouched
                # product copies. A candidate must never certify its own LM as
                # reducible merely because it has already entered a cache.
                actions=[action for action in actions
                         if p.encode(p.primitive(action[0])[0]) not in excluded_identities]
            if not actions:
                b.add_term(out, head, pending.pop(head))
                continue
            rel, source = actions[-1 if reverse else 0]
            ah, rh = pending[head], rel[head]
            assert all(b.mkey(m) < b.mkey(head) for m in rel if m != head)
            pending = p.subtract(pending, ah, rel, rh)
            if rh != b.ONE:
                out = poly_scale(out, rh)
                den = b.pmul(den, rh)
            count += 1
            if trace:
                steps.append({'input': head, 'source': source, 'identity': rel,
                              'input_coefficient': ah, 'leading_coefficient': rh})
            if count > max_steps:
                raise RuntimeError('Reduction step limit exceeded; no result claimed.')
        self.stats['reduction_steps'] += count
        return out, den, steps

    def candidate_term_actions(self, row):
        """Every term, not just the LM, must be checked before registration.

        Call before adding the candidate itself. Original identities are retained
        by convention; this gate applies to generated S-polynomial remainders.
        """
        return [(mon,actions[0]) for mon in sorted(row,key=b.mkey,reverse=True)
                if (actions:=self.actions(mon,first_only=True))]

    def assess_descendant(self, row, excluded_identities=frozenset()):
        """Strategy-A retention test against the established rules in this engine.

        Exclude the candidate itself (and, if supplied, circular dependent rules).
        If another established replacement reduces its original contextual LM,
        this context is omitted from the descendant list. A nonzero consistency
        remainder must be handled by S-polynomial completion, not relabelled as
        a descendant with a different LM.
        """
        row,_,_=p.primitive(row)
        if not row:return {'retain':False,'reason':'zero_context','steps':[]}
        head=max(row,key=b.mkey)
        excluded=set(excluded_identities)|{p.encode(row)}
        numerator,den,steps=self.reduce({head:b.ONE},trace=True,
                                        excluded_identities=excluded)
        if steps:
            return {'retain':False,'reason':'LM_reduced_by_other_rule',
                    'head':head,'LM_remainder':numerator,'denominator':den,'steps':steps}
        reduced,den,steps=self.reduce(row,trace=True,excluded_identities=excluded)
        assert head in reduced and max(reduced,key=b.mkey)==head
        return {'retain':True,'reason':'LM_survives','head':head,
                'identity':reduced,'denominator':den,'steps':steps}

    def actions(self, mon, first_only=False):
        key=(self.version,mon,first_only)
        if key in self.action_cache:
            self.stats['action_cache_hits']+=1
            return self.action_cache[key]
        try:
            result=self._actions(mon,first_only)
        except FirstAction as found:
            result=[found.action]
        self.action_cache[key]=result
        return result

    def _actions(self, mon, first_only=False):
        key = (self.version, mon, first_only)
        if key in self.action_cache:
            self.stats['action_cache_hits'] += 1
            return self.action_cache[key]
        self.stats['input_monomials_examined'] += 1
        if first_only:
            momentum=self.momentum_actions(mon)
            if momentum:
                return momentum[:1]
        actions = []
        seen = {}
        def accept(row, rest, source):
            if not row:
                return
            row, common, scale = p.primitive(row)
            whole = p.multiply(row, b.mono(rest + common))
            if not whole or max(whole, key=b.mkey) != mon:
                return
            enc = p.encode(whole)
            if enc in seen:
                previous=seen[enc]
                ids=set(previous.get('equivalent_parent_ids',[previous['parent']]))
                ids.update(source.get('equivalent_parent_ids',[source['parent']]))
                previous['equivalent_parent_ids']=sorted(ids)
                return
            source = dict(source)
            seen[enc]=source
            source['coefficient_scale_removed'] = scale
            actions.append((whole, source))
            h = max(row, key=b.mkey)
            rec = (row, source)
            row_encoding=p.encode(row)
            if row_encoding not in self.cache_encodings[h]:
                self.cache[h].append(rec)
                self.cache_encodings[h].add(row_encoding)
                self.stats['cached_contextual_replacements'] += 1
            if first_only:
                raise FirstAction(actions[-1])
        # Stored descendants are used only as untouched tensor-product factors.
        # A further contraction is matched and reoriented below, not inherited.
        for k in range(1, len(mon)+1):
            for pos in combinations(range(len(mon)), k):
                h = tuple(mon[i] for i in pos)
                rest = p.quotient(mon, h)
                for row, source in list(self.cache.get(h, ())):
                    accept(row, rest, source)
        if mon not in self.original_cache:
            original=[]
            for row,rest,source in self.original_candidates(mon):
                original.append((row,rest,source))
                if source['kind']=='S':
                    rkey=p.encode(row)
                    if rkey in self.momentum_polynomial_cache:
                        self.stats['momentum_polynomial_cache_hits']+=1
                    else:
                        self.momentum_polynomial_cache[rkey]=self.reduce(row,only_m=True,trace=True)
                    reduced,den,steps=self.momentum_polynomial_cache[rkey]
                    if reduced and p.encode(reduced)!=p.encode(row):
                        original.append((reduced,rest,{**source,'momentum_reduced':True,
                                              'momentum_steps':steps,'denominator':den}))
            self.original_cache[mon]=original
        for row,rest,source in self.original_cache[mon]:
            accept(row,rest,source)
        ml,mb,me=b.graph(mon)
        input_signature=Counter((c,tuple(sorted((ml[a],ml[z])))) for a,z,c in mb)
        for pid, ti, pattern, signature in self.matching_derived_patterns(mon, input_signature):
            if len(pattern[1]) >= p.degree(mon) or any(input_signature[k]<v for k,v in signature.items()):
                continue
            parent = self.parents[pid]
            dkey=(pid,ti,mon)
            if dkey in self.derived_context_cache:
                for contextual,rest,source in self.derived_context_cache[dkey]:
                    accept(contextual,rest,source)
                continue
            materialized=[]
            _,_,_,owners,_=graph_details(mon)
            contexts_seen=set()
            for selected, mapping in graph_matches(pattern, mon):
                block, rest, edge_selection = selected_block(mon, selected)
                touched={owners[e] for e in selected}
                old_edges=[i for i in range(len(mb)) if owners[i] in touched]
                renumber={v:i for i,v in enumerate(old_edges)}
                local_map={v:2*renumber[w//2]+w%2 for v,w in mapping.items()}
                csig=(block,edge_selection,tuple(sorted(local_map.items())))
                if csig in contexts_seen:continue
                contexts_seen.add(csig)
                contextual = self.embedded_derived_identity(parent, ti, pattern, block, edge_selection, local_map)
                self.stats['derived_contexts_materialized'] += 1
                source={'parent': pid, 'kind': 'derived-context',
                                          'block': block, 'pattern_term': ti,
                                          'selected_edges': edge_selection, 'port_map': local_map}
                materialized.append((contextual,rest,source))
                accept(contextual,rest,source)
            self.derived_context_cache[dkey]=materialized
        self.action_cache[key] = actions
        return actions


def serial(value):
    if isinstance(value, dict):
        if value and not all(isinstance(k, str) for k in value):
            return [[serial(k), serial(v)] for k,v in value.items()]
        return {k: serial(v) for k,v in value.items()}
    if isinstance(value, (tuple,list)):
        return [serial(x) for x in value]
    return value


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(serial(value), separators=(',',':')), encoding='utf-8')
    temp.replace(path)


def read_row(row):
    return {freeze(m): {tuple(e): v for e,v in c} for m,c in row}


def bp_factor(value):
    return freeze(value)
