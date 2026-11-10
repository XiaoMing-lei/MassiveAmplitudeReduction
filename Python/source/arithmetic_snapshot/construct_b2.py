"""B2 parent-pair construction with selective reversed-context extensions.

Original M/S identities are retained. Contexts are not promoted to parents.
Only actual contextual LMs may be cancelled; no amplitude basis is constructed.
Historical A and B-prime implementations are preserved.
"""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
from time import perf_counter
import gzip
import json
import pickle
import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from optimized_bprime import OptimizedReducer
from construct_bprime import external_children, contextual_lms_match
from construct_bprime_lm_gated import unresolved_schouten_slots
from construct_bprime_unique_momentum import UniqueMomentumConstruction


class B2Reducer(OptimizedReducer):
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
                raise bp.FirstAction(actions[-1])
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
                        if max(reduced, key=b.mkey) == max(row, key=b.mkey):
                            original.append((reduced,rest,{**source,'momentum_reduced':True,
                                                  'momentum_steps':steps,'denominator':den}))
                        else:
                            # A changed contextual head is an M-S consistency
                            # remainder, never a descendant of S with a new head.
                            self.stats['changed_S_heads_not_cached_as_descendants'] += 1
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
            _,_,_,owners,_=bp.graph_details(mon)
            contexts_seen=set()
            for selected, mapping in bp.graph_matches(pattern, mon):
                block, rest, edge_selection = bp.selected_block(mon, selected)
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


class B2Construction(UniqueMomentumConstruction):
    def __init__(self, n, degree, out, seconds=0):
        super().__init__(n, degree, seconds, '_b2')
        self.out = Path(out)
        self.engine = B2Reducer(n, degree, unique_momentum_lm=True)
        self.exclusions = []
        self.extension_examples = []
        self.report_options.update(strategy='B2',
            parent_and_output_degree_cap=degree, common_input_degree_cap=degree,
            exhaustive_descendant_pair_queue=False,
            changed_S_head_may_not_be_relabelled_as_descendant=True)

    @staticmethod
    def source_ids(source):
        return set(source.get('equivalent_parent_ids', [source['parent']]))

    def contextual_overlap(self, mon, origin, pair, seen):
        todo = [(mon, [])]
        while todo:
            # Optional pause/checkpoint hook, between complete cancellations.
            # It changes no matching, orientation, or exclusion decision.
            if hasattr(self, 'control'):
                self.control()
            host, path = todo.pop()
            if host in seen:
                continue
            seen.add(host)
            tick = perf_counter()
            actions = self.engine.actions(host)
            self.timings['pair_orientation_seconds'] += perf_counter() - tick
            pair_ids = set(pair)
            actual = [pid for row, source in actions for pid in self.source_ids(source)]
            # Exclude both participating parents: their own proposed reductions
            # cannot establish that the overlap was eliminated by another rule.
            other = next(((r, s) for r, s in actions
                          if self.source_ids(s).isdisjoint(pair_ids)), None)
            if other is not None:
                self.exclusions.append((host, pair, other[1]['parent'],
                    self.engine.parents[other[1]['parent']]['revision']))
                self.stats['overlaps_discarded_LM_reduced_by_other_parent'] += 1
                # Do not allow A-B, A-C and B-C to discard one another.
                # Replace the proposed A-B cancellation by checks against a
                # single established reference C. They are still parent
                # cancellations in this input, not a descendant-pair queue.
                # Once C-A and C-B are resolved, A-B is covered algebraically.
                if host not in self.host_branches:
                    reference, reference_source = other
                    self.host_branches[host] = (reference, reference_source,
                                                {p.encode(reference)})
                self.check_host(host, {**origin, 'common_context': path,
                    'B2_discarded_pair': pair,
                    'B2_consistency_reference': self.host_branches[host][1]['parent']})
                self.stats['excluded_overlaps_with_reference_checks'] += 1
                continue
            exposed = (all(pid in actual for pid in pair) if pair[0] != pair[1]
                       else actual.count(pair[0]) >= 2)
            if exposed:
                self.stats['actual_LM_pair_inputs'] += 1
                self.check_host(host, {**origin, 'common_context': path,
                    'requested_pair_has_actual_LMs': True,
                    'B2_other_parent_LM_gate_passed': True})
            else:
                missing = [pid for pid in pair_ids if pid not in actual]
                # An original M has only its prescribed LM. No attachments
                # are searched to rescue another term of that identity.
                if any(self.engine.parents[pid]['family'] == 'M' for pid in missing):
                    self.stats['prescribed_M_nonleading_stops'] += 1
                    continue
                if not missing:
                    self.stats['identical_single_occurrence_stops'] += 1
                    continue
                if p.degree(host) >= self.window:
                    self.stats['unresolved_at_degree_bound'] += 1
                    continue
                required = []
                for pid in missing:
                    parent = self.engine.parents[pid]
                    if parent['family'] == 'S':
                        slots = unresolved_schouten_slots(host, tuple(parent['labels']))
                        if slots:
                            required.append(slots)
                slots = min(required, key=len) if required else ()
                self.stats['unresolved_tie_extensions' if slots else
                           'reversed_orientation_extensions'] += 1
                if not slots and len(self.extension_examples) < 50:
                    self.extension_examples.append({'input':host,'pair':pair,
                        'missing_parents':missing,'context':path,'origin':origin})
                for child, attachment in external_children(host, self.n, slots):
                    if child not in seen and p.degree(child) <= self.window:
                        todo.append((child, path + [attachment]))
            if perf_counter() - self.last_progress > 30:
                self.checkpoint('running_B2', self.stage, full=False)
            if self.seconds and perf_counter() - self.start > self.seconds:
                raise TimeoutError('B2 finite queue incomplete; checkpoint retained.')

    def checkpoint(self, status, stage, full=True):
        active = [r for r in self.engine.parents if r['active']]
        report = dict(particles=self.n, degree=self.degree, status=status, stage=stage,
            seconds=perf_counter()-self.start, parents=len(active),
            originals=sum(r['raw'] is not None for r in active),
            parent_degrees=dict(Counter(max(map(p.degree,r['row']),default=2) for r in active)),
            historical_parent_records=len(self.engine.parents), stats=dict(self.stats),
            reducer_stats=dict(self.engine.stats), timings=dict(self.timings), rounds=self.rounds,
            no_basis_enumeration=True, **self.report_options)
        self.out.mkdir(parents=True, exist_ok=True)
        if full:
            tick = perf_counter()
            archive = dict(exclusions=self.exclusions,
                reversal_examples=self.extension_examples,
                context_cache=dict(self.engine.cache),
                checked_inputs=self.host_seen,
                resolved_cancellations=self.resolved_cancellations)
            with gzip.open(self.out/'search_archive.pkl.gz','wb',compresslevel=1) as stream:
                pickle.dump(archive,stream,protocol=5)
            bp.save(self.out/'catalog.json',dict(summary=report,parents=active,
                history_records=self.engine.parents,journal=self.engine.journal,
                full_search_archive='search_archive.pkl.gz'))
            self.timings['checkpoint_io_seconds'] += perf_counter()-tick
        report.update(seconds=perf_counter()-self.start,timings=dict(self.timings))
        report['construction_compute_seconds'] = report['seconds']-self.timings['checkpoint_io_seconds']
        bp.save(self.out/'progress.json',report)
        self.last_progress=perf_counter()
        if full:self.last_save=self.last_progress
        print(json.dumps({k:report[k] for k in ('status','stage','seconds','parents','parent_degrees')}),flush=True)
        return report


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=6)
    ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=float,default=0)
    args=ap.parse_args()
    task=B2Construction(args.particles,args.degree,args.out,args.seconds)
    try:task.run()
    except TimeoutError:task.checkpoint('time_limit_partial',task.stage)


if __name__=='__main__':main()

