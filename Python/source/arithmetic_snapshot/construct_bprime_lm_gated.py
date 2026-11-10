"""B' construction: extend unresolved indexed Schoutens, not definite non-LMs.

Uses the existing staged/backward-reduced constructor and tensor order. No
amplitude basis construction. The previous constructor is preserved unchanged.

Known coverage limitation (2026-10-23): ending a resolved overlap branch can
omit an ambiguity after one more momentum-forming contraction. See
audit_record304_context.py and n4_d8_unique_momentum/OMITTED_DEGREE_SIX_OVERLAP.md.
Queue completion is not exhaustive bounded confluence. The pruning below is
preserved to keep the recorded runs reproducible, pending a stability-aware fix.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
from time import perf_counter

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_bprime import external_children
from construct_bprime_interreduced import InterreducedConstruction


@lru_cache(None)
def unresolved_schouten_slots(mon, parent_labels):
    """Untouched equal-particle free slots in matching Schouten occurrences.

    Only these indexed-permutation ambiguities justify growing a context. An
    already oriented nonleading occurrence is not a reason to attach a bracket.
    Distinct occurrences are considered separately; a resolved occurrence must
    not hide another occurrence whose equal-particle slots are still free.
    """
    chirality, *labels = parent_labels
    repeated = [i for i, count in Counter(labels).items() if count == 2]
    if not repeated:
        return ()
    ll, bb, ee = b.graph(mon)
    occupied = {v for edge in ee for v in edge}
    required = set()
    for first, second in combinations(range(len(bb)), 2):
        if bb[first][2] != chirality or bb[second][2] != chirality:
            continue
        ports = bb[first][:2] + bb[second][:2]
        if sorted(ll[v] for v in ports) != labels:
            continue
        untouched = [tuple(v for v in ports if ll[v] == i) for i in repeated
                     if all(v not in occupied for v in ports if ll[v] == i)]
        if untouched:
            # At least one of this pair must be touched to expose this occurrence.
            required.update(untouched[0])
    return tuple(sorted(required))


class LMGatedConstruction(InterreducedConstruction):
    def __init__(self, n, degree, seconds=600, tag='_lm_gated'):
        super().__init__(n, degree, seconds, tag)
        self.stopped_examples = []

    def extension_slots(self, host, pair, actual):
        required = []
        for pid in set(pair):
            if pid in actual:
                continue
            parent = self.engine.parents[pid]
            if parent['family'] != 'S' or parent['raw'] is None:
                return None, pid
            slots = unresolved_schouten_slots(host, tuple(parent['labels']))
            if not slots:
                return None, pid
            required.append(slots)
        # A self-pair with only one actual occurrence is not an unresolved tie.
        if not required:
            return None, pair[0]
        return min(required, key=len), None

    def contextual_overlap(self, mon, origin, pair, seen):
        todo = [(mon, [])]
        while todo:
            host, path = todo.pop()
            if host in seen:
                continue
            seen.add(host)
            tick = perf_counter()
            actions = self.engine.actions(host)
            self.timings['pair_orientation_seconds'] += perf_counter() - tick
            actual = [pid for row, source in actions
                      for pid in source.get('equivalent_parent_ids', [source['parent']])]
            exposed = (all(pid in actual for pid in pair) if pair[0] != pair[1]
                       else actual.count(pair[0]) >= 2)
            if exposed:
                self.stats['actual_LM_pair_inputs'] += 1
                # The actual parents are applicable before any S-polynomial is
                # constructed. Other valid reductions of this same input can
                # share the cancellation check, as in the previous constructor.
                self.check_host(host, {**origin, 'common_context': path,
                                       'requested_pair_has_actual_LMs': True})
            else:
                required, failed = self.extension_slots(host, pair, actual)
                if required is None:
                    self.stats['definite_nonleading_pair_stops'] += 1
                    if len(self.stopped_examples) < 100:
                        self.stopped_examples.append({'input': host, 'origin': origin,
                            'context': path, 'requested_parents': pair,
                            'actual_parents': actual, 'stopped_parent': failed})
                elif p.degree(host) < self.window:
                    self.stats['unresolved_Schouten_context_extensions'] += 1
                    for child, attachment in external_children(host, self.n, required):
                        if child not in seen and p.degree(child) <= self.window:
                            todo.append((child, path + [attachment]))
                else:
                    self.stats['unresolved_at_degree_bound'] += 1
            if perf_counter() - self.last_progress > 30:
                self.checkpoint('running', self.stage,
                                full=perf_counter() - self.last_save > 120)
            if self.seconds and perf_counter() - self.start > self.seconds:
                raise TimeoutError('Saved finite-window partial checkpoint.')

    def checkpoint(self, status, stage, full=True):
        report = super().checkpoint(status, stage, full)
        if full:
            bp.save(self.out / 'context_gate.json', {
                'policy': 'Require both selected parents to be actual contextual LMs; '
                          'extend only unresolved repeated-particle Schouten occurrences.',
                'stopped_examples': self.stopped_examples,
                'no_nonleading_M_or_derived_context_extensions': True})
        return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--particles', type=int, default=4)
    ap.add_argument('--degree', type=int, default=4)
    ap.add_argument('--seconds', type=float, default=600)
    ap.add_argument('--tag', default='_lm_gated')
    args = ap.parse_args()
    task = LMGatedConstruction(args.particles, args.degree, args.seconds, args.tag)
    try:
        task.run()
    except TimeoutError:
        task.checkpoint('time_limit_partial', task.stage)


if __name__ == '__main__':
    main()
