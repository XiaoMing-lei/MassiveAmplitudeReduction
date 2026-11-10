"""Exact search/cache optimizations, with unchanged order and allowed matches.

These primitives serve both A-construction checks and frozen B applications.
They do not implement descendant enumeration or certify overlap coverage.
"""
from collections import Counter, defaultdict
from contextlib import contextmanager
import json
from pathlib import Path

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_bprime_interreduced import VersionedReducer


class LazyExcludedCache(dict):
    """Same filtered cache as without_parent, materialized only for touched heads."""
    def __init__(self, original, parent):
        super().__init__()
        self.original = original
        self.parent = parent

    def __missing__(self, head):
        value = [(row, src) for row, src in self.original.get(head, ())
                 if src['parent'] != self.parent]
        self[head] = value
        return value

    def get(self, head, default=None):
        return self[head]


class LazyEncodings(dict):
    def __init__(self, cache):
        super().__init__()
        self.cache = cache

    def __missing__(self, head):
        result = {p.encode(row) for row, src in self.cache[head]}
        self[head] = result
        return result


class OptimizedReducer(VersionedReducer):
    def matching_derived_patterns(self, mon, input_signature):
        stamp = (self.version, len(self.derived_patterns))
        if (getattr(self, '_pattern_object', None) is not self.derived_patterns or
                getattr(self, '_pattern_stamp', None) != stamp):
            self._pattern_object = self.derived_patterns
            self._pattern_stamp = stamp
            frequencies = Counter(k for pid, ti, graph, sig in self.derived_patterns for k in sig)
            self._pattern_postings = defaultdict(list)
            for ordinal, entry in enumerate(self.derived_patterns):
                sig = entry[3]
                anchor = min(sig, key=lambda k: (frequencies[k], k))
                self._pattern_postings[anchor].append((ordinal, sig[anchor], entry))
            self._signature_candidates = {}
            self.stats['pattern_index_builds'] += 1
        signature_key = tuple(sorted(input_signature.items()))
        if signature_key not in self._signature_candidates:
            degree = p.degree(mon)
            selected = []
            for key, count in input_signature.items():
                for ordinal, minimum, entry in self._pattern_postings.get(key, ()):
                    if count >= minimum and len(entry[2][1]) < degree and all(
                            input_signature[k] >= v for k, v in entry[3].items()):
                        selected.append((ordinal, entry))
            selected.sort(key=lambda item: item[0])
            if len(self._signature_candidates) >= 10000:
                self._signature_candidates.clear()
            self._signature_candidates[signature_key] = tuple(entry for _, entry in selected)
            self.stats['pattern_signature_misses'] += 1
        else:
            self.stats['pattern_signature_hits'] += 1
        return self._signature_candidates[signature_key]

    def embedded_derived_identity(self, parent, ti, pattern, block, edges, port_map):
        if not hasattr(self, '_block_embeddings'):
            self._block_embeddings = {}
        key = (parent['id'], parent.get('revision', 0), ti, block, edges,
               tuple(sorted(port_map.items())))
        if key not in self._block_embeddings:
            if len(self._block_embeddings) >= 100000:
                self._block_embeddings.clear()
            self._block_embeddings[key] = bp.embed_physical(
                parent['row'], pattern, block, edges, port_map)
            self.stats['minimal_block_embedding_misses'] += 1
        else:
            self.stats['minimal_block_embedding_hits'] += 1
        return self._block_embeddings[key]

    @contextmanager
    def without_parent(self, pid):
        saved = (self.cache, self.cache_encodings, self.action_cache, self.derived_patterns)
        self.cache = LazyExcludedCache(self.cache, pid)
        self.cache_encodings = LazyEncodings(self.cache)
        self.action_cache = {}
        self.derived_patterns = [entry for entry in self.derived_patterns if entry[0] != pid]
        try:
            yield
        finally:
            self.cache, self.cache_encodings, self.action_cache, self.derived_patterns = saved


def compact_package(data):
    """Retain all active parents; proofs remain in the full construction archive."""
    return {'summary': data['summary'], 'runtime_only': True,
            'parents': [{key: rec[key] for key in ('id', 'family', 'labels', 'raw', 'row', 'revision')}
                        for rec in data['parents']],
            'construction_archive_required_for_proofs': True,
            'matching_policy': 'All active parents and the same potential-LM algorithm; '
                               'contextual substitutions computed on demand. No completion at query time.'}


def load_frozen(data, optimized=True, input_degree=None):
    n = data['summary']['particles']
    degree = input_degree or data['summary']['degree']
    cls = OptimizedReducer if optimized else VersionedReducer
    engine = cls(n, degree, unique_momentum_lm=data['summary'].get('unique_momentum_lm', False))
    engine.parents = []
    engine.original_ids = {}
    for saved in data['parents']:
        while len(engine.parents) < saved['id']:
            engine.parents.append({'id': len(engine.parents), 'raw': None, 'row': {},
                                   'active': False, 'revision': 0})
        rec = dict(saved)
        rec['row'] = bp.read_row(saved['row'])
        rec['raw'] = bp.freeze(saved['raw']) if saved['raw'] is not None else None
        rec.update(active=True, verified_epochs={})
        engine.parents.append(rec)
        if rec['raw'] is not None:
            engine.original_ids[rec['family'], tuple(rec['labels'])] = rec['id']
        else:
            for ti, graph in engine.parent_patterns(rec):
                labels, brackets, eps = graph
                signature = Counter((c, tuple(sorted((labels[a], labels[z]))))
                                    for a, z, c in brackets)
                engine.derived_patterns.append((rec['id'], ti, graph, signature))
            head = max(rec['row'], key=b.mkey)
            engine.cache[head].append((rec['row'], {'parent': rec['id'], 'kind': 'derived-product'}))
            engine.cache_encodings[head].add(p.encode(rec['row']))
    # A factor-cancelled descendant can have an LM that contains no direct
    # embedding of the parent's pattern. Preserve these exact replacements.
    engine.load_cached_descendants(data.get('descendants', []))
    return engine
