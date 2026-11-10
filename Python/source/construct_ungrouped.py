"""Fresh group-independent construction; classify only final presentations.

Keeps the v3.2 order and eligible-LM filter. All reductions and overlap
reference choices ignore groups. Uses minimal parent overlaps, the agreed
parent/output cutoff and early irreducible-above-bound discard.
"""
import argparse
import gzip
import json
import os
import pickle
from collections import Counter
from pathlib import Path
from time import perf_counter
import strict_stages as base
from construct_bprime_interreduced import VersionedReducer
from construct_b2 import B2Construction
from unbolded_rule_groups import rule_group

b, bp, p = base.b, base.bp, base.p


class UngroupedReducer(base.StrictReducer):
    def __init__(self, n, degree):
        super().__init__(n, degree, unique_momentum_lm=True)
        for rec in self.parents:
            rec.pop('origin_group', None)

    def actions(self, mon, first_only=False):
        return base.old.V32Reducer.actions(self, mon, first_only)

    def add_parent(self, row, source):
        key = p.encode(p.primitive(row)[0])
        for rec in self.parents:
            if rec['raw'] is not None and p.encode(p.primitive(rec['row'])[0]) == key:
                rec.setdefault('alternative_derived_proofs', []).append(source)
                self.stats['duplicate_original_derivations_not_registered'] += 1
                return rec['id'], False
        return VersionedReducer.add_parent(self, row, source)

    def replace_parent(self, pid, row, proof):
        return VersionedReducer.replace_parent(self, pid, row, proof)

    def reduce(self, row, only_m=False, reverse=False, trace=False,
               max_steps=200000, excluded_identities=frozenset(), degree_bound=None):
        pending, out, den, steps = dict(row), {}, b.ONE, []
        count = 0
        while pending:
            if hasattr(self, 'budget_check'):
                self.budget_check()
            head = max(pending, key=b.mkey)
            actions = (self.momentum_actions(head, all_actions=reverse or bool(excluded_identities))
                       if only_m else self.actions(head, first_only=not reverse and not excluded_identities))
            if excluded_identities:
                actions = [(r,s) for r,s in actions
                           if p.encode(p.primitive(r)[0]) not in excluded_identities]
            if not actions:
                if degree_bound is not None and p.degree(head) > degree_bound:
                    self.stats['early_above_degree_stops'] += 1
                    raise base.AboveDegreeRemainder(head, degree_bound, None, count)
                b.add_term(out, head, pending.pop(head))
                continue
            rel, source = actions[-1 if reverse else 0]
            assert max(rel, key=b.mkey) == head
            assert all(b.mkey(m) < b.mkey(head) for m in rel if m != head)
            ah, rh = pending[head], rel[head]
            pending = p.subtract(pending, ah, rel, rh)
            if rh != b.ONE:
                out = bp.poly_scale(out, rh)
                den = b.pmul(den, rh)
            count += 1
            if trace:
                steps.append({'input': head, 'source': source, 'identity': rel,
                              'input_coefficient': ah, 'leading_coefficient': rh})
            if count > max_steps:
                raise RuntimeError('Reduction step limit')
        self.stats['reduction_steps'] += count
        return out, den, steps

    def interreduce(self):
        updates = 0
        while True:
            changed = False
            active = [r for r in self.parents if r['raw'] is None and r['active']]
            active.sort(key=lambda r:(max(map(p.degree,r['row'])), r['id']))
            for rec in active:
                self.budget_check()
                row, pid = rec['row'], rec['id']
                degree = max(map(p.degree,row))
                dirty = [d for d,v in self.epochs.items() if d <= degree
                         and rec['verified_epochs'].get(d,0) != v]
                if not dirty:
                    self.stats['unchanged_degree_epochs_skipped'] += 1
                    continue
                threshold = min(dirty)
                with self.without_parent(pid):
                    if not self.candidate_term_actions({m:co for m,co in row.items() if p.degree(m)>=threshold}):
                        rec['verified_epochs'] = dict(self.epochs)
                        continue
                    result, den, steps = self.reduce(row, trace=True)
                    normalized, factor, scale = p.primitive(result)
                    while normalized and self.candidate_term_actions(normalized):
                        result, d2, more = self.reduce(result, trace=True)
                        if not more:
                            raise RuntimeError('Primitive match requires explicit factor replay')
                        den = b.pmul(den, d2); steps += more
                        normalized, factor, scale = p.primitive(result)
                self.replace_parent(pid, normalized, {'trigger_degree':threshold,
                    'reduction_steps':steps, 'denominator':den,
                    'removed_product':factor, 'removed_scale':scale,
                    'group_independent_interreduction':True})
                updates += 1; changed = True
            if not changed:
                return updates


class UngroupedConstruction(base.StrictConstruction):
    def __init__(self, n, degree, out, seconds):
        super().__init__(n, degree, out, seconds)
        self.engine = UngroupedReducer(n, degree)
        self.engine.budget_check = self.control
        self.report_options.update(revision='ungrouped_construction',
            construction_groups=False, origin_groups=None,
            candidate_interreduction='All established replacements, independent of groups',
            execution='Classify final prepared rules by maximum-degree unbolded products',
            search_revision='ungrouped_minimal_parent_overlaps',
            timing_scope='Fresh initialization, generation, interreduction and preparation; validation separate')
        self.prepared = []

    def checkpoint(self, status, stage, full=True):
        if status.startswith('running') and perf_counter()-self.last_save < 900:
            full = False
        # Bypass the historical ancestry-classification checkpoint wrapper.
        return B2Construction.checkpoint(self, status, stage, full)

    def check_host(self, mon, origin):
        self.control()
        if self.host_seen.get(mon) == self.engine.version:
            return self.engine.actions(mon)
        self.host_seen[mon] = self.engine.version
        self.stats['distinct_input_checks'] += 1
        actions = self.engine.actions(mon)
        self.host_exposed[mon] = [pid for _,s in actions
            for pid in s.get('equivalent_parent_ids',[s['parent']])]
        if len(actions) < 2:
            return actions
        first, source = actions[0]
        for other, other_source in actions[1:]:
            self.control()
            assert base.contextual_lms_match(mon, first, other)
            fm, om = p.primitive(first)[0], p.primitive(other)[0]
            if p.quotient(mon, b.mono(max(fm,key=b.mkey)+max(om,key=b.mkey))) is not None:
                self.stats['disjoint_product_ambiguities_skipped'] += 1
                continue
            sp = p.subtract(first, first[mon], other, other[mon])
            if not sp:
                continue
            primitive_sp, sp_factor, sp_scale = p.primitive(sp)
            sp_key = p.encode(primitive_sp)
            if sp_key in self.resolved_cancellations:
                self.stats['repeated_factor_multiples_skipped'] += 1
                continue
            stamp = self.reduction_stamp()
            if self.deferred_stamp != stamp:
                self.deferred_remainders.clear(); self.deferred_stamp = stamp
            if sp_key in self.deferred_remainders:
                self.stats['unchanged_above_degree_reductions_reused'] += 1
                continue
            tick = perf_counter()
            try:
                remainder, den, steps = self.engine.reduce(primitive_sp, trace=True, degree_bound=self.window)
            except base.AboveDegreeRemainder as stop:
                self.timings['S_reduction_seconds'] += perf_counter()-tick
                self.stats['S_polynomials'] += 1
                self.stats['early_above_degree_discards'] += 1
                self.stats['steps_before_early_discard'] += stop.steps
                if self.reduction_stamp() == stamp:
                    self.deferred_remainders[sp_key] = True
                continue
            self.timings['S_reduction_seconds'] += perf_counter()-tick
            self.stats['S_polynomials'] += 1
            row, factor, scale = p.primitive(remainder)
            while row and self.engine.candidate_term_actions(row):
                remainder, d2, more = self.engine.reduce(remainder, trace=True)
                if not more:
                    raise RuntimeError('Primitive-only match requires factor replay')
                den = b.pmul(den,d2); steps += more
                row, factor, scale = p.primitive(remainder)
            if not row:
                self.stats['zero_remainders'] += 1
            elif max(map(p.degree,row)) <= self.window:
                proof = {'overlap':origin, 'common_input':mon,
                    'left_identity':first, 'right_identity':other,
                    'left_source':source, 'right_source':other_source,
                    'S_polynomial':sp, 'primitive_S_polynomial':primitive_sp,
                    'S_common_factor':sp_factor, 'S_coefficient_scale':sp_scale,
                    'reduction_steps':steps, 'denominator':den,
                    'removed_product':factor, 'removed_scale':scale,
                    'all_terms_interreduced_without_groups':True}
                pid, new = self.engine.add_parent(row,proof)
                if new:
                    self.stats['additional_parents'] += 1
            else:
                self.stats['over_degree_remainders'] += 1
            self.resolved_cancellations.add(sp_key)
        return actions

    def prepare_contexts(self):
        """Prepare encountered replacements within the retained input bound.

        This is finite encountered-context coverage, not all tensor inputs.
        Ordinary M applications stay separate. No basis candidates are used.
        """
        records = {}
        for head, entries in list(self.engine.cache.items()):
            if p.degree(head) > self.degree:
                continue
            for row, source in entries:
                if source['kind'] in ('M', 'derived-product'):
                    continue
                records.setdefault(p.encode(row), (row, source))
        self.prepared = []; omitted = []
        for key,(row,source) in records.items():
            self.control()
            head = max(row,key=b.mkey)
            available = self.engine.actions(head)
            def reference_key(action):
                primitive = p.primitive(action[0])[0]
                return p.degree(max(primitive,key=b.mkey)), p.encode(primitive)
            reference = min(available,key=reference_key) if available else (row,source)
            reference_encoding = p.encode(p.primitive(reference[0])[0])
            if reference_encoding != key:
                # Resolve the consistency comparison; do not relabel a
                # changed-head remainder as the same descendant.
                self.check_host(head, {'descendant_preparation':source})
                omitted.append({'source':source, 'identity':row,
                                'head_reduced_by':reference[1],
                                'reference_identity':reference[0]})
                continue
            tail = {m:c for m,c in row.items() if m != head}
            reduced,den,steps = self.engine.reduce(tail,trace=True,
                                                  excluded_identities={key})
            b.add_term(reduced,head,b.pmul(row[head],den))
            prepared,factor,scale = p.primitive(reduced)
            assert prepared and max(prepared,key=b.mkey) == p.quotient(head,factor)
            self.prepared.append({'parent_source':source, 'original_identity':row,
                'identity':prepared, 'rhs_reduction_steps':steps, 'denominator':den,
                'removed_product':factor, 'removed_scale':scale,
                'group':rule_group(prepared)})
        self.stats['encountered_contexts_for_preparation'] = len(records)
        self.stats['omitted_reducible_contexts'] = len(omitted)
        bp.save(self.out/'prepared_contexts.json', {'scope':'Encountered contexts of degree <= D',
            'retained':self.prepared, 'omitted':omitted,
            'ordinary_M_applications_not_descendants':True})

    def run(self):
        self.window = 2
        for parent in list(self.engine.parents):
            for ti,pattern in self.engine.parent_patterns(parent):
                ll,bb,ee = pattern
                for extra in base.matchings(ll,bb,ee):
                    for mon in b.normalize_graph(ll,bb,ee+extra):
                        self.check_host(mon, {'parent':parent['id'],'term':ti,'closure':extra})
        for window in range(2,self.degree+1):
            self.window = window
            for number in range(1,21):
                tick = perf_counter(); before = len(self.engine.parents)
                self.reset_overlap_checks(); self.run_window(0)
                ti = perf_counter(); changed = self.engine.interreduce()
                self.timings['backward_reduction_seconds'] += perf_counter()-ti
                self.rounds.append({'parent_degree':window,'round':number,
                    'insertions':len(self.engine.parents)-before,'presentation_updates':changed,
                    'active_parents':sum(r['active'] for r in self.engine.parents),
                    'seconds':perf_counter()-tick})
                self.checkpoint('backward_pass_finished',{'parent_degree':window,'round':number})
                if not changed:
                    break
            else:
                raise RuntimeError('No presentation fixed point after 20 passes')
            self.checkpoint('parent_stage_completed',{'parent_degree':window})
        before = len(self.engine.parents)
        self.stage = {'parent_degree':self.degree,'phase':'context_preparation'}
        tick = perf_counter(); self.prepare_contexts()
        self.timings['context_preparation_seconds'] += perf_counter()-tick
        if len(self.engine.parents) != before:
            return self.checkpoint('preparation_generated_parent_requires_more_overlaps',self.stage)
        groups = []
        for rec in self.engine.parents:
            if not rec['active']:
                continue
            group = rule_group(rec['row']) if rec['row'] else 2
            groups.append({'id':rec['id'],'family':rec['family'],
                           'original':rec['raw'] is not None,'group':group,
                           'degree':max(map(p.degree,rec['row']),default=2)})
        bp.save(self.out/'final_groups.json',groups)
        return self.checkpoint('completed_finite_parent_queue_and_encountered_contexts',
                               {'parent_degree':self.degree})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--particles',type=int,default=4)
    parser.add_argument('--degree',type=int,default=4)
    parser.add_argument('--seconds',type=float,default=25)
    parser.add_argument('--out',required=True)
    args = parser.parse_args(); out = Path(args.out)
    if out.exists():
        raise RuntimeError('Fresh output directory required')
    out.mkdir(parents=True)
    task = UngroupedConstruction(args.particles,args.degree,out,args.seconds)
    (out/'construction_source.py').write_bytes(Path(__file__).read_bytes())
    bp.save(out/'process.json',{'pid':os.getpid(),'status':'running'})
    try:
        report = task.run()
        bp.save(out/'process.json',{'pid':os.getpid(),'status':report['status']})
    except BaseException as exc:
        status = 'time_limit_partial' if isinstance(exc,TimeoutError) else 'error_partial'
        task.checkpoint(status,task.stage)
        bp.save(out/'process.json',{'pid':os.getpid(),'status':status})
        (out/'error.txt').write_text(repr(exc)+'\n',encoding='utf-8')
        if not isinstance(exc,TimeoutError):
            raise


if __name__ == '__main__':
    main()
