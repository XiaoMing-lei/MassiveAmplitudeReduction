"""Fresh bounded v3.2 construction; never loads a historical rule catalog."""
import argparse
from collections import Counter
from pathlib import Path
from time import perf_counter
import json
import sys

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
# Dependencies are installed in the active Python environment.
sys.path.insert(0, str(HERE / 'arithmetic_snapshot'))
import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_b2 import B2Construction
from fast_contextual_matching import FastContextReducer
from efficient_b2_restart import install_engine_caches
import ssyt_order as ordering

_configure = bp.configure


def configure(n, degree):
    _configure(n, degree)
    ordering.install(b)


bp.configure = configure


class V32Reducer(FastContextReducer):
    def __init__(self, n, degree, unique_momentum_lm=True):
        super().__init__(n, degree, unique_momentum_lm=unique_momentum_lm)
        install_engine_caches(self)
        for rec in self.parents:
            rec['origin_group'] = (1 if rec['family'] == 'M' or
                                   len(set(rec['labels'][1:])) == 4 else 2)

    def source_group(self, source):
        if not source:
            return 2
        ids = source.get('equivalent_parent_ids', [source.get('parent')])
        groups = [self.parents[i].get('origin_group', 1)
                  for i in ids if i is not None]
        groups += [self.source_group(s.get('source', {}))
                   for s in source.get('momentum_steps', [])]
        return 1 if 1 in groups else 2

    def proof_group(self, proof):
        groups = [self.source_group(proof.get(k, {}))
                  for k in ('left_source', 'right_source')]
        groups += [self.source_group(s.get('source', {}))
                   for s in proof.get('reduction_steps', [])]
        return 1 if 1 in groups else 2

    def add_parent(self, row, source):
        group = self.proof_group(source or {})
        pid, new = super().add_parent(row, source)
        if new:
            self.parents[pid]['origin_group'] = group
            self.parents[pid]['top_behavior'] = ordering.top_behavior(row)
        return pid, new

    def replace_parent(self, pid, row, proof):
        group = min(self.parents[pid]['origin_group'], self.proof_group(proof))
        super().replace_parent(pid, row, proof)
        self.parents[pid]['origin_group'] = group
        self.parents[pid]['top_behavior'] = ordering.top_behavior(row)

    def reduce(self, row, only_m=False, reverse=False, trace=False, max_steps=200000,
               excluded_identities=frozenset()):
        if only_m:
            return super().reduce(row, only_m=True, reverse=reverse, trace=trace,
                                  max_steps=max_steps,
                                  excluded_identities=excluded_identities)
        pending, out, den, steps = dict(row), {}, b.ONE, []
        count = 0
        previous_phase = {}
        while pending:
            degree = max(map(p.degree, pending))
            heads = sorted((m for m in pending if p.degree(m) == degree),
                           key=b.mkey, reverse=True)
            selected = None
            second = []
            for head in heads:
                actions = self.actions(head, first_only=False)
                if excluded_identities:
                    actions = [a for a in actions if
                               p.encode(p.primitive(a[0])[0]) not in excluded_identities]
                if reverse:
                    actions = list(reversed(actions))
                for rel, source in actions:
                    group = self.source_group(source)
                    behavior = ordering.top_behavior(rel)
                    if group == 2 and behavior == 'changes_unbolded':
                        raise RuntimeError('Pure repeated-Schouten consequence changes '
                                           'the prepared top product; stage definition needs review.')
                    candidate = (head, rel, source, group, behavior)
                    if group == 1:
                        selected = candidate
                        break
                    second.append(candidate)
                if selected:
                    break
            if selected is None and second:
                selected = second[-1 if reverse else 0]
            if selected is None:
                for head in heads:
                    b.add_term(out, head, pending.pop(head))
                continue
            head, rel, source, phase, behavior = selected
            if previous_phase.get(degree) == 2 and phase == 1:
                self.stats['stage_one_reentries_after_stage_two'] += 1
            previous_phase[degree] = phase
            ah, rh = pending[head], rel[head]
            assert all(b.mkey(m) < b.mkey(head) for m in rel if m != head)
            pending = p.subtract(pending, ah, rel, rh)
            if rh != b.ONE:
                out = bp.poly_scale(out, rh)
                den = b.pmul(den, rh)
            count += 1
            self.stats[f'v32_stage_{phase}_steps'] += 1
            if trace:
                steps.append({'input': head, 'source': {**source, 'origin_group': phase},
                              'identity': rel, 'input_coefficient': ah,
                              'leading_coefficient': rh, 'stage': phase,
                              'top_behavior': behavior})
            if count > max_steps:
                raise RuntimeError('Step cap reached; no normal-form claim.')
        self.stats['reduction_steps'] += count
        return out, den, steps


class V32Construction(B2Construction):
    def __init__(self, n, degree, out, seconds=0):
        super().__init__(n, degree, out, seconds)
        self.engine = V32Reducer(n, degree)
        self.report_options.update(version='3.2',
            order='degree_then_global_massless_tableau_order_then_contractions',
            fresh_originals_only=True, old_catalog_loaded=False,
            origin_groups='1: M or distinct-S ancestry; 2: repeated-S only',
            execution='degree staged, group 1 then group 2; reentries reported')

    def checkpoint(self, status, stage, full=True):
        result = super().checkpoint(status, stage, full)
        active = [r for r in self.engine.parents if r['active']]
        bp.save(self.out / 'v3_2_groups.json', {
            'version': '3.2',
            'origins': dict(Counter(r['origin_group'] for r in active)),
            'records': [{'id': r['id'], 'origin_group': r['origin_group'],
                         'family': r['family'], 'labels': r['labels'],
                         'degree': max(map(p.degree, r['row']), default=2),
                         'top_behavior': ordering.top_behavior(r['row'])}
                        for r in active],
            'reentries': self.engine.stats['stage_one_reentries_after_stage_two'],
            'not_an_unrestricted_completion_certificate': True})
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--particles', type=int, required=True)
    parser.add_argument('--degree', type=int, required=True)
    parser.add_argument('--out', required=True)
    parser.add_argument('--seconds', type=float, default=0)
    args = parser.parse_args()
    out = Path(args.out).resolve()
    if (out / 'catalog.json').exists():
        raise RuntimeError('Choose a fresh output directory; historical results are preserved.')
    task = V32Construction(args.particles, args.degree, out, args.seconds)
    try:
        task.run()
    except TimeoutError:
        task.checkpoint('time_limit_partial', task.stage)
    except Exception as exc:
        task.checkpoint('error_partial', task.stage)
        (out / 'error.txt').write_text(repr(exc) + '\n', encoding='utf-8')
        raise


if __name__ == '__main__':
    main()
