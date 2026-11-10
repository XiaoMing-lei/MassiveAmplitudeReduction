"""v3.2 revision: unbolded-LM filtering and separately completed rule groups.

Historical v3.2 runs and the arithmetic snapshot are not modified.
"""
import argparse
from collections import Counter, defaultdict
import gzip
import hashlib
from itertools import combinations
import json
import os
from pathlib import Path
import pickle
import subprocess
import sys
from time import perf_counter

import run_v3_2 as old
from construct_bprime import contextual_lms_match, overlap_inputs, external_children, matchings
from construct_bprime_lm_gated import unresolved_schouten_slots
from construct_bprime_interreduced import InterreducedConstruction
from benchmark_bprime import grouped_tex
from efficient_b2_restart import BoundedCache

b, bp, p, ordering = old.b, old.bp, old.p, old.ordering


def graph_prefix(graph):
    labels, brackets, contractions = graph
    edges=[]
    for a,z,c in brackets:
        i,j=sorted((labels[a],labels[z]))
        edges.append((c,i,j) if c else (c,-i,-j))
    return len(brackets),tuple(sorted(edges))


def leading_patterns(parent, unique_momentum_lm=True):
    patterns=list(bp.parent_patterns(parent,unique_momentum_lm))
    if not patterns:
        return
    if parent['family']=='M':
        yield from patterns
        return
    best=max(graph_prefix(graph) for _,graph in patterns)
    yield from ((ti,graph) for ti,graph in patterns if graph_prefix(graph)==best)


def load_strict(data,archive_path=None):
    from optimized_bprime import load_frozen
    old.configure(data['summary']['particles'],2*data['summary']['degree'])
    engine=load_frozen(data)
    engine.__class__=StrictReducer
    engine.factor_contexts_seen=set()
    engine.derived_patterns=[]
    for rec in engine.parents:
        if rec['raw'] is not None or not rec['active']:continue
        for ti,graph in engine.parent_patterns(rec):
            ll,bb,ee=graph
            signature=Counter((c,tuple(sorted((ll[a],ll[z])))) for a,z,c in bb)
            engine.derived_patterns.append((rec['id'],ti,graph,signature))
    old.install_engine_caches(engine)
    if archive_path is not None:
        with gzip.open(archive_path,'rb') as stream:
            saved=pickle.load(stream)
        engine.cache=defaultdict(list,saved['context_cache'])
        engine.cache_encodings=defaultdict(set,
            {h:{p.encode(row) for row,source in rows} for h,rows in engine.cache.items()})
    return engine


class StageCoverageGap(RuntimeError):
    pass


class AboveDegreeRemainder(Exception):
    def __init__(self, head, bound, group, steps):
        self.head,self.bound,self.group,self.steps=head,bound,group,steps
        super().__init__(f'Irreducible degree {p.degree(head)} term above {bound}, group {group}')


class StrictReducer(old.V32Reducer):
    def __init__(self,n,degree,unique_momentum_lm=True):
        super().__init__(n,degree,unique_momentum_lm)
        self.factor_contexts_seen=set()

    def parent_patterns(self,parent):
        return leading_patterns(parent,self.unique_momentum_lm)

    def original_candidates(self,mon,only_m=False):
        for row,rest,source in super().original_candidates(mon,only_m):
            if source['kind']=='S':
                parent=self.parents[source['parent']]
                if len(set(parent['labels'][1:]))==4:
                    ll,bb,ee=b.graph(source['block'])
                    selected=[bb[i] for i in source['placement']]
                    selected_key=graph_prefix((ll,selected,()))
                    permitted=max(graph_prefix(g) for _,g in self.parent_patterns(parent))
                    if selected_key!=permitted:
                        self.stats['nonleading_distinct_S_occurrences_skipped']+=1
                        continue
            yield row,rest,source

    def actions(self,mon,first_only=False):
        # A new primitive replacement discovered on a proper disconnected
        # factor may change previous matches. Re-encountering one already
        # cached must not invalidate the queue. Snapshot actual cache lengths,
        # not a second bookkeeping set of previously seen polynomials.
        heads={tuple(mon[i] for i in pos)
               for k in range(1,len(mon)) for pos in combinations(range(len(mon)),k)}
        before={head:len(self.cache.get(head,())) for head in heads}
        actions=super().actions(mon,first_only)
        added=[(head,len(self.cache.get(head,()))-count)
               for head,count in before.items() if len(self.cache.get(head,()))>count]
        new_degrees={p.degree(head) for head,count in added}
        if new_degrees:
            self.version+=1
            self.action_cache.clear()
            for degree in new_degrees:self.epochs[degree]+=1
            self.stats['new_factor_cancelled_application_records']+=sum(count for head,count in added)
        return actions

    def matching_may_have_changed(self,mon,previous_version):
        return self.version!=previous_version

    def group_actions(self,mon,group,excluded_identities=frozenset()):
        return [(row,source) for row,source in self.actions(mon)
                if self.source_group(source)==group and
                (not excluded_identities or
                 p.encode(p.primitive(row)[0]) not in excluded_identities)]

    def reduce_group(self,row,group,trace=False,reverse=False,
                     excluded_identities=frozenset(),guard_second=False,degree_bound=None):
        pending,out,den,steps=dict(row),{},b.ONE,[]
        count=0
        while pending:
            if hasattr(self,'budget_check'):self.budget_check()
            head=max(pending,key=b.mkey)
            actions=self.group_actions(head,group,excluded_identities)
            if not actions:
                if degree_bound is not None and p.degree(head)>degree_bound:
                    self.stats['early_above_degree_stops']+=1
                    raise AboveDegreeRemainder(head,degree_bound,group,count)
                b.add_term(out,head,pending.pop(head));continue
            rel,source=actions[-1 if reverse else 0]
            assert max(rel,key=b.mkey)==head
            assert all(b.mkey(m)<b.mkey(head) for m in rel if m!=head), 'Non-strict contraction order'
            ah,rh=pending[head],rel[head]
            pending=p.subtract(pending,ah,rel,rh)
            if rh!=b.ONE:
                out=bp.poly_scale(out,rh);den=b.pmul(den,rh)
            count+=1
            if trace:
                steps.append({'input':head,'source':{**source,'origin_group':group},
                    'identity':rel,'input_coefficient':ah,'leading_coefficient':rh,
                    'stage':group,'top_behavior':ordering.top_behavior(rel)})
            if guard_second:
                for m in rel:
                    if m!=head and self.group_actions(m,1):
                        self.last_stage_gap={'input':head,'second_identity':rel,
                            'second_source':source,'exposed':m}
                        raise StageCoverageGap('A group-2 replacement exposes a group-1 LM; '
                                               'no return to group 1 was performed.')
            if count>200000:raise RuntimeError('Reduction step limit')
        self.stats[f'strict_group_{group}_steps']+=count
        return out,den,steps

    def reduce(self,row,only_m=False,reverse=False,trace=False,max_steps=200000,
               excluded_identities=frozenset()):
        if only_m:
            return super().reduce(row,only_m=True,reverse=reverse,trace=trace,
                max_steps=max_steps,excluded_identities=excluded_identities)
        first,d1,s1=self.reduce_group(row,1,trace,reverse,excluded_identities)
        second,d2,s2=self.reduce_group(first,2,trace,reverse,excluded_identities,
                                       guard_second=True)
        return second,b.pmul(d1,d2),s1+s2

    def candidate_group_actions(self,row,group):
        return [(m,actions[0]) for m in sorted(row,key=b.mkey,reverse=True)
                if (actions:=self.group_actions(m,group))]

    def reduce_candidate(self,row,group,degree_bound=None):
        # First-stage consequences must not be erased by second-stage rules.
        # A proposed second-stage identity, however, must first be reduced by
        # the already established first-stage rules. Otherwise a repeated-S
        # derivation of an original distinct-S would be registered twice.
        # Establish whether a group-2 candidate uses any group-1 reduction
        # before applying a degree stop in its permitted reduction group.
        uses_first=group==1 or any(self.group_actions(m,1)
                                 for m in sorted(row,key=b.mkey,reverse=True))
        if uses_first:
            first,den,steps=self.reduce_group(row,1,trace=True,degree_bound=degree_bound)
            return first,den,steps,1
        second,den,steps=self.reduce_group(row,2,trace=True,degree_bound=degree_bound)
        return second,den,steps,2

    def add_parent(self,row,source):
        group=self.proof_group(source or {})
        primitive=p.primitive(row)[0]
        key=p.encode(primitive)
        for original in self.parents:
            if original['raw'] is not None and p.encode(p.primitive(original['row'])[0])==key:
                original.setdefault('alternative_derived_proofs',[]).append(source)
                self.stats['duplicate_original_derivations_not_registered']+=1
                return original['id'],False
        if group==2 and ordering.top_behavior(primitive)=='changes_unbolded':
            raise StageCoverageGap('A repeated-Schouten-only remainder changes the unbolded product; '
                                   'it cannot be registered as a second-group rule.')
        pid,new=super().add_parent(row,source)
        if not new and group==1 and self.parents[pid].get('origin_group')==2:
            rec=self.parents[pid]
            rec.setdefault('alternative_group1_proofs',[]).append(source)
            rec['origin_group']=1
            self.version+=1;self.action_cache.clear()
            self.epochs[max(map(p.degree,rec['row']))]+=1
            self.stats['parent_group_promotions']+=1
        return pid,new

    def interreduce(self):
        updates=0
        while True:
            changed=False
            active=[r for r in self.parents if r['raw'] is None and r['active']]
            active.sort(key=lambda r:(max(map(p.degree,r['row'])),r['origin_group'],r['id']))
            for rec in active:
                if hasattr(self,'budget_check'):self.budget_check()
                group=rec['origin_group'];row=rec['row'];pid=rec['id']
                with self.without_parent(pid):
                    applicable=self.candidate_group_actions(row,group)
                    if group==2:applicable+=self.candidate_group_actions(row,1)
                    if not applicable:continue
                    result,den,steps,result_group=self.reduce_candidate(row,group)
                    normalized,factor,scale=p.primitive(result)
                    assert not self.candidate_group_actions(normalized,result_group)
                self.replace_parent(pid,normalized,{'trigger_degree':max(map(p.degree,row)),
                    'reduction_steps':steps,'denominator':den,'removed_product':factor,
                    'removed_scale':scale,'interreduction_group':result_group})
                updates+=1;changed=True
            if not changed:break
        return updates


class StrictConstruction(old.V32Construction):
    def __init__(self,n,degree,out,seconds=0):
        super().__init__(n,degree,out,seconds)
        # The comparator must cover common inputs above the parent cutoff.
        # Extra zero coordinates leave every lower-degree comparison unchanged.
        old.configure(n,2*degree)
        self.engine=StrictReducer(n,degree)
        self.engine.budget_check=self.control
        self.report_options.update(revision='strict_stages',
            potential_LMs='Only maximum degree and unbolded-product terms before unions',
            execution='All group 1, then group 2; a new group-1 match is a coverage error',
            candidate_interreduction='Within candidate proof group; mixed proofs belong to group 1')
        self.report_options.update(parent_LM_and_retained_remainder_cutoff=degree,
            common_input_degree_cap=None,
            common_overlap_cutoff_is_not_parent_cutoff=True,
            initial_overlaps='All minimal unions of eligible LM patterns, through their summed degree',
            spectator_context_limit='No further extensions of minimal parent overlaps',
            search_revision='minimal_B2_early_discard_actual_cache_changes',
            early_discard='Stop at the first irreducible above-bound term before later factor removal',
            contraction_comparison_maximum_length=2*degree)
        self.next_control=0
        self.deferred_remainders=BoundedCache(25000)
        self.deferred_stamp=None
        self.use_deferred_cache=True
        self.resume_cursor=None
        self.prior_seconds=0

    def reduction_stamp(self):
        # Context-cache additions can alter the available replacements even
        # without inserting a parent. Reuse only an exactly unchanged state.
        return (self.window,self.engine.version,
                self.engine.stats['cached_contextual_replacements'])

    def restore_partial(self,path,extend=False):
        path=Path(path);data=json.loads(path.read_text(encoding='utf-8'))
        summary=data['summary']
        assert summary['revision']=='strict_stages'
        assert summary['common_overlap_cutoff_is_not_parent_cutoff']
        assert summary['particles']==self.n
        if extend:
            assert summary['degree']<self.degree
            assert summary['status']=='completed_parent_cutoff_queue'
            verification=json.loads((path.parent/'verification.json').read_text(encoding='utf-8'))
            assert verification.get('passed',False), 'Extend only a verified lower window'
        else:
            assert summary['degree']==self.degree
            assert summary['status']=='paused_partial'
        self.engine=load_strict(data)
        self.engine.budget_check=self.control
        old.configure(self.n,2*self.degree)
        self.engine.degree=self.degree
        # Preserve inactive records and complete derivation histories too.
        history=data.get('history_records',data['parents'])
        for saved in history:
            if not saved.get('active',True):
                rec=dict(saved);rec['row']=bp.read_row(rec['row'])
                while len(self.engine.parents)<=rec['id']:
                    self.engine.parents.append({})
                self.engine.parents[rec['id']]=rec
        self.engine.journal=list(data.get('journal',[]))
        with gzip.open(path.parent/data['full_search_archive'],'rb') as stream:
            archive=pickle.load(stream)
        self.engine.cache=defaultdict(list,archive['context_cache'])
        self.engine.cache_encodings=defaultdict(set,
            {head:{p.encode(row) for row,source in records}
             for head,records in self.engine.cache.items()})
        self.stats=Counter(summary['stats'])
        self.timings=Counter(dict(summary['timings']))
        self.engine.stats=Counter(summary['reducer_stats'])
        self.rounds=list(summary['rounds'])
        self.prior_seconds=summary['seconds']+summary.get('prior_construction_seconds',0)
        self.resume_cursor=({'parent_degree':summary['degree']+1,'left_parent':0,'right_parent':0}
                            if extend else dict(summary['stage']))
        self.exclusions=archive.get('exclusions',[])
        self.extension_examples=archive.get('reversal_examples',[])
        self.report_options.update(fresh_originals_only=False,
            resumes_strict_parent_cutoff=str(path.resolve()),
            base_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            prior_construction_seconds=self.prior_seconds,
            timing_scope='seconds: resumed segment; timings: cumulative measured work',
            preserved_parent_records=len(self.engine.parents))

    def control(self):
        if perf_counter()<self.next_control:return
        self.next_control=perf_counter()+0.1
        if self.seconds and perf_counter()-self.start>=self.seconds:
            raise TimeoutError(f'Construction limit {self.seconds:.6f}s reached')
        path=self.out/'control.json'
        if path.exists() and json.loads(path.read_text()).get('action')=='pause':
            raise InterruptedError('Cooperative pause requested')

    def checkpoint(self,status,stage,full=True):
        if status.startswith('running') and perf_counter()-self.last_save<900:full=False
        report=super().checkpoint(status,stage,full)
        if self.prior_seconds:
            report['cumulative_construction_seconds']=self.prior_seconds+report['seconds']
            report['construction_compute_seconds']=report['cumulative_construction_seconds']-self.timings['checkpoint_io_seconds']
            bp.save(self.out/'progress.json',report)
        return report

    def contextual_overlap(self,mon,origin,pair,seen):
        self.control()
        if mon in seen:return
        seen.add(mon)
        tick=perf_counter();actions=self.engine.actions(mon)
        self.timings['pair_orientation_seconds']+=perf_counter()-tick
        self.stats['minimal_overlap_contexts_checked']+=1
        if len(actions)>=2:
            self.check_host(mon,{**origin,'common_context':[]})
        else:self.stats['minimal_overlaps_without_two_actual_LMs']+=1

    def run_window(self,start,right_start=0):
        i=start
        while i<len(self.engine.parents):
            left=self.engine.parents[i]
            if not left['active'] or max(map(p.degree,left['row']),default=2)>self.window:
                i+=1;continue
            lp=list(self.engine.parent_patterns(left))
            for j in range(right_start if i==start else 0,i+1):
                self.control()
                right=self.engine.parents[j]
                if not right['active'] or max(map(p.degree,right['row']),default=2)>self.window:continue
                self.stage={'parent_degree':self.window,'left_parent':i,'right_parent':j}
                self.stats['parent_pairs']+=1;seen=set()
                for ti,a in lp:
                    for tj,c in self.engine.parent_patterns(right):
                        tick=perf_counter()
                        # A minimal union cannot contain more brackets than
                        # the two patterns combined. No cap at self.window.
                        for mon,witness in overlap_inputs(a,c,len(a[1])+len(c[1])):
                            self.timings['input_generation_seconds']+=perf_counter()-tick
                            if i==j and ti==tj and witness['shared_brackets']==len(a[1]):
                                self.stats['identical_occurrence_pairs_skipped']+=1;tick=perf_counter();continue
                            if mon not in seen:
                                self.stats['overlaps_above_parent_degree']+=int(p.degree(mon)>self.window)
                                self.contextual_overlap(mon,{'parents':[i,j],'terms':[ti,tj],**witness},(i,j),seen)
                            tick=perf_counter()
                        self.timings['input_generation_seconds']+=perf_counter()-tick
                if perf_counter()-self.last_progress>30:self.checkpoint('running',self.stage,full=False)
            i+=1

    def run(self):
        self.window=2
        if self.resume_cursor is None:
            for parent in list(self.engine.parents):
                for ti,pattern in self.engine.parent_patterns(parent):
                    ll,bb,ee=pattern
                    for extra in matchings(ll,bb,ee):
                        for mon in b.normalize_graph(ll,bb,ee+extra):
                            self.check_host(mon,{'parent':parent['id'],'term':ti,'closure':extra})
        first_window=self.resume_cursor['parent_degree'] if self.resume_cursor else 2
        for window in range(first_window,self.degree+1):
            self.window=window
            round_number=max((r['round'] for r in self.rounds if r['parent_degree']==window),default=0)
            while True:
                round_number+=1;start=perf_counter()
                before=len(self.engine.parents);version=self.engine.version
                self.reset_overlap_checks()
                resumed_tail=self.resume_cursor is not None
                if resumed_tail:
                    cursor=self.resume_cursor;self.resume_cursor=None
                    # Repeat the interrupted pair, then require a whole pass.
                    self.run_window(cursor['left_parent'],cursor['right_parent'])
                else:self.run_window(0)
                tick=perf_counter();changed=self.engine.interreduce()
                self.timings['backward_reduction_seconds']+=perf_counter()-tick
                inserted=len(self.engine.parents)-before
                self.rounds.append({'parent_degree':window,'round':round_number,
                    'insertions':inserted,'presentation_updates':changed,
                    'active_parents':sum(r['active'] for r in self.engine.parents),
                    'seconds':perf_counter()-start,'resumed_tail':resumed_tail})
                self.checkpoint('backward_pass_finished',{'parent_degree':window,'round':round_number})
                # Above-bound remainders were not retained. Revisit the old
                # pairs after any new applicable replacement: an old remainder
                # may now reduce below the retained-degree bound.
                if not resumed_tail and not changed and self.engine.version==version:break
            self.checkpoint('parent_stage_completed',{'parent_degree':window,'rounds':round_number})
        return self.checkpoint('completed_parent_cutoff_queue',{'parent_degree':self.degree})

    def check_host(self,mon,origin):
        if self.host_seen.get(mon)==self.engine.version:
            return self.engine.actions(mon)
        self.host_seen[mon]=self.engine.version
        self.stats['distinct_input_checks']+=1
        actions=self.engine.actions(mon)
        self.host_exposed[mon]=[pid for _,s in actions
            for pid in s.get('equivalent_parent_ids',[s['parent']])]
        if len(actions)<2:return actions
        # A first-group reference makes all mixed comparisons explicit.
        actions=sorted(actions,key=lambda a:self.engine.source_group(a[1]))
        first,source=actions[0]
        for other,other_source in actions[1:]:
            if not contextual_lms_match(mon,first,other):
                raise AssertionError('Nonleading S-polynomial cancellation')
            first_min=p.primitive(first)[0];other_min=p.primitive(other)[0]
            if p.quotient(mon,b.mono(max(first_min,key=b.mkey)+max(other_min,key=b.mkey))) is not None:
                self.stats['disjoint_product_ambiguities_skipped']+=1;continue
            sp=p.subtract(first,first[mon],other,other[mon])
            if not sp:continue
            group=min(self.engine.source_group(source),self.engine.source_group(other_source))
            primitive_sp,sp_factor,sp_scale=p.primitive(sp)
            sp_key=(group,p.encode(primitive_sp))
            if sp_key in self.resolved_cancellations:
                self.stats['repeated_factor_multiples_skipped']+=1;continue
            stamp=self.reduction_stamp()
            if self.deferred_stamp!=stamp:
                self.deferred_remainders.clear();self.deferred_stamp=stamp
            if self.use_deferred_cache and sp_key in self.deferred_remainders:
                self.stats['unchanged_above_degree_reductions_reused']+=1;continue
            tick=perf_counter()
            try:
                remainder,den,steps,group=self.engine.reduce_candidate(
                    primitive_sp,group,degree_bound=self.window)
            except AboveDegreeRemainder as stop:
                self.timings['S_reduction_seconds']+=perf_counter()-tick
                self.stats['S_polynomials']+=1
                self.stats['early_above_degree_discards']+=1
                self.stats['steps_before_early_discard']+=stop.steps
                if self.use_deferred_cache and self.reduction_stamp()==stamp:
                    self.deferred_remainders[sp_key]=True
                continue
            self.timings['S_reduction_seconds']+=perf_counter()-tick
            self.stats['S_polynomials']+=1
            if not remainder:
                self.stats['zero_remainders']+=1
                self.resolved_cancellations.add(sp_key);continue
            row,factor,scale=p.primitive(remainder)
            # Factor removal may expose a previously saved contextual match.
            # Keep the additional reduction in the certificate.
            while (self.engine.candidate_group_actions(row,group) or
                   (group==2 and self.engine.candidate_group_actions(row,1))):
                # Normalize only after completing the fraction-free replay.
                remainder,d2,more,group=self.engine.reduce_candidate(remainder,group)
                den=b.pmul(den,d2);steps+=more
                row,factor,scale=p.primitive(remainder)
                if not more:raise RuntimeError('Primitive-only match requires explicit factor replay')
            if not row:
                self.stats['zero_remainders']+=1
                self.resolved_cancellations.add(sp_key);continue
            if max(map(p.degree,row))>self.window:
                self.stats['over_degree_remainders']+=1
                if self.use_deferred_cache and self.reduction_stamp()==stamp:
                    self.deferred_remainders[sp_key]=True
                continue
            proof={'overlap':origin,'common_input':mon,'left_identity':first,
                'right_identity':other,'left_source':source,'right_source':other_source,
                'S_polynomial':sp,'primitive_S_polynomial':primitive_sp,
                'S_common_factor':sp_factor,'S_coefficient_scale':sp_scale,
                'reduction_steps':steps,'denominator':den,'removed_product':factor,
                'removed_scale':scale,'interreduction_group':group,
                'all_terms_irreducible_in_group_before_registration':True}
            pid,new=self.engine.add_parent(row,proof)
            if new:
                self.stats['additional_parents']+=1
                print(f'parent {pid}: group {group}, degree {max(map(p.degree,row))}, '
                      f'{perf_counter()-self.start:.3f}s',flush=True)
            self.resolved_cancellations.add(sp_key)
        return actions


def audit_pair(out):
    old.configure(4,4)
    engine=StrictReducer(4,4)
    a=engine.parents[engine.original_ids['S',(1,1,2,3,4)]]
    s=engine.parents[engine.original_ids['S',(0,3,3,4,4)]]
    def candidates(filtered):
        rows={}
        ap=list(leading_patterns(a)) if filtered else list(bp.parent_patterns(a,True))
        sp=list(leading_patterns(s)) if filtered else list(bp.parent_patterns(s,True))
        for ti,pa in ap:
            for tj,ps in sp:
                for mon,witness in overlap_inputs(pa,ps,4):rows.setdefault(mon,{'terms':[ti,tj],**witness})
        return rows
    before=candidates(False);after=candidates(True)
    assert len(before)==12 and len(after)==4
    unrestricted=old.V32Reducer(4,4)
    lost_actual=[];rows=[]
    for mon,witness in before.items():
        actual=[(rel,src) for rel,src in unrestricted.actions(mon)
                if a['id'] in src.get('equivalent_parent_ids',[src['parent']])]
        if actual and mon not in after:lost_actual.append(mon)
        rows.append({'input':mon,'tex':grouped_tex({mon:b.ONE}),
                     'retained':mon in after,'distinct_S_actual_LM':bool(actual)})
    assert not lost_actual
    report={'before':12,'after':4,'filtered_angle_pattern':list(leading_patterns(a)),
            'lost_actual_distinct_S_occurrences':lost_actual,'candidates':rows}
    bp.save(out,report)
    print(json.dumps({'pair_audit':str(out),'before':12,'after':4}))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--particles',type=int)
    parser.add_argument('--degree',type=int)
    parser.add_argument('--out',required=True)
    parser.add_argument('--audit-pair',action='store_true')
    parser.add_argument('--seconds',type=float,default=0)
    parser.add_argument('--resume')
    parser.add_argument('--base')
    parser.add_argument('--verify-after',action='store_true')
    args=parser.parse_args()
    if args.audit_pair:
        audit_pair(Path(args.out));return
    out=Path(args.out)
    if (out/'catalog.json').exists():raise RuntimeError('Fresh output folder required')
    task=StrictConstruction(args.particles,args.degree,out,args.seconds)
    if args.resume and args.base:raise RuntimeError('Choose resume or extension, not both')
    if args.resume:task.restore_partial(args.resume)
    if args.base:task.restore_partial(args.base,extend=True)
    out.mkdir(parents=True,exist_ok=True)
    bp.save(out/'process.json',{'pid':os.getpid(),'status':'running'})
    try:
        task.run()
        bp.save(out/'process.json',{'pid':os.getpid(),'status':'construction_finished'})
        if args.verify_after:
            subprocess.run([sys.executable,str(Path(__file__).with_name('verify_strict_stages.py')),
                            '--catalog',str(out/'catalog.json')],check=True)
            verified=json.loads((out/'verification.json').read_text(encoding='utf-8'))['passed']
            bp.save(out/'process.json',{'pid':os.getpid(),'status':
                'construction_and_verification_finished' if verified else 'verification_failed'})
    except BaseException as exc:
        status=('time_limit_partial' if isinstance(exc,TimeoutError) else
                'paused_partial' if isinstance(exc,(KeyboardInterrupt,InterruptedError)) else 'error_partial')
        task.checkpoint(status,task.stage)
        bp.save(out/'process.json',{'pid':os.getpid(),'status':status})
        (out/'error.txt').write_text(repr(exc)+'\n')
        raise


if __name__=='__main__':main()
