"""Group-independent completion with degree-priority S-polynomials.

Parent pairs are revisited only for new/changed parent presentations.
Nonzero above-bound stops are saved and reopened when their head can reduce.
New cached product replacements reopen only previously inspected inputs that
contain their exact tensor-product head. No basis enumeration is performed.
"""
import argparse
import gzip
import heapq
import json
import os
import pickle
from collections import Counter, defaultdict
from pathlib import Path
from time import perf_counter
import construct_ungrouped as prior

base, b, bp, p = prior.base, prior.b, prior.bp, prior.p


class QueueReducer(prior.UngroupedReducer):
    def add_parent(self,row,source):
        pid,new=super().add_parent(row,source)
        if new and hasattr(self,'presentation_event'):
            self.presentation_event(pid,'insert')
        return pid,new

    def replace_parent(self,pid,row,proof):
        old=self.parents[pid]['row']
        steps=proof['reduction_steps']
        if steps and steps[0]['input']==max(old,key=b.mkey):
            step=steps[0];head=step['input'];other=step['identity']
            cancellation=p.subtract(old,old[head],other,other[head])
            proof={**proof,'same_LM_cancellation':{
                'common_LM':head,'left_identity':old,'right_identity':other,
                'retained_reference':step['source'],
                'S_polynomial':cancellation,
                'old_parent':pid,'old_revision':self.parents[pid]['revision']}}
            self.stats['explicit_same_LM_backward_cancellations']+=1
        super().replace_parent(pid,row,proof)
        if hasattr(self,'presentation_event'):
            self.presentation_event(pid,'update')

    def reduce(self,row,only_m=False,reverse=False,trace=False,max_steps=200000,
               excluded_identities=frozenset(),degree_bound=None,potential_only=False):
        pending,out,den,steps=dict(row),{},b.ONE,[];count=0
        while pending:
            if hasattr(self,'budget_check'):self.budget_check()
            head=max(pending,key=b.mkey)
            # Once an irreducible top product survives, only its contraction
            # variants can still be potential heads. Preserve the entire tail.
            if potential_only and out:
                import ssyt_order
                top=max(out,key=b.mkey)
                if ssyt_order.unbolded(head)!=ssyt_order.unbolded(top):
                    for mon,co in pending.items():b.add_term(out,mon,co)
                    pending.clear()
                    break
            actions=(self.momentum_actions(head,all_actions=reverse or bool(excluded_identities))
                if only_m else self.actions(head,first_only=not reverse and not excluded_identities))
            if excluded_identities:
                actions=[(r,s) for r,s in actions
                         if p.encode(p.primitive(r)[0]) not in excluded_identities]
            if not actions:
                if degree_bound is not None and p.degree(head)>degree_bound:
                    self.stats['early_above_degree_stops']+=1
                    stop=base.AboveDegreeRemainder(head,degree_bound,None,count)
                    stop.partial_row=dict(pending)
                    for m,co in out.items():b.add_term(stop.partial_row,m,co)
                    stop.denominator=den;stop.reduction_steps=steps
                    raise stop
                b.add_term(out,head,pending.pop(head));continue
            rel,source=actions[-1 if reverse else 0]
            assert max(rel,key=b.mkey)==head
            assert all(b.mkey(m)<b.mkey(head) for m in rel if m!=head)
            ah,rh=pending[head],rel[head]
            pending=p.subtract(pending,ah,rel,rh)
            if rh!=b.ONE:out=bp.poly_scale(out,rh);den=b.pmul(den,rh)
            count+=1
            if trace:steps.append({'input':head,'source':source,'identity':rel,
                                  'input_coefficient':ah,'leading_coefficient':rh})
            if count>max_steps:raise RuntimeError('Reduction step limit')
        self.stats['reduction_steps']+=count
        return out,den,steps


class DegreeQueueConstruction(prior.UngroupedConstruction):
    def __init__(self,n,degree,out,seconds=0):
        super().__init__(n,degree,out,seconds)
        self.engine=QueueReducer(n,degree)
        self.engine.budget_check=self.control
        self.engine.presentation_event=self.presentation_event
        self.pair_heap=[];self.pair_scheduled=set();self.pair_done=set()
        self.s_heap=[];self.tasks={};self.counter=0
        self.blocked=defaultdict(set)
        self.input_postings=defaultdict(set);self.registered_inputs=set()
        self.known_cache_polynomials=set();self.pending_host_checks=set()
        self.presentations_dirty=False;self.blocked_match_version=-1
        self.current_pair=None;self.current_task=None
        self.collision_records=[]
        self.resumed=False
        self.next_progress=perf_counter()+30
        self.report_options.update(revision='degree_queue_construction',
            queue_order='Current raw/remainder S-polynomial degree; lower degrees first',
            pair_rechecks='Only pairs involving a new or changed parent presentation',
            cached_context_rechecks='Only existing inputs divisible by a newly cached product head',
            above_bound_work='Deferred with exact partial reduction certificate; never silently deleted',
            construction_limit_seconds=seconds,
            timing_scope='Fresh construction and encountered-context preparation; verification separate')
        for parent in self.engine.parents:self.schedule_parent(parent['id'])

    def control(self):
        super().control()
        if hasattr(self,'next_progress') and perf_counter()>=self.next_progress:
            self.next_progress=perf_counter()+30
            self.checkpoint('running_degree_queue',self.stage,full=False)

    def restore_queue(self):
        """Resume the saved finite queue; repeat only interrupted operations."""
        tick=perf_counter()
        data=json.loads((self.out/'catalog.json').read_text())
        summary=json.loads((self.out/'progress.json').read_text())
        assert summary['status'] in ('paused_partial','error_partial','time_limit_partial')
        assert (summary['particles'],summary['degree'])==(self.n,self.degree)
        self.engine=base.load_strict(data,self.out/'search_archive.pkl.gz')
        self.engine.__class__=QueueReducer
        self.engine.budget_check=self.control
        self.engine.presentation_event=self.presentation_event
        for saved in data['history_records']:
            rec=dict(saved);rec['row']=bp.read_row(rec['row'])
            rec['raw']=bp.freeze(rec['raw']) if rec['raw'] is not None else None
            rec['verified_epochs']={}
            while len(self.engine.parents)<=rec['id']:self.engine.parents.append({})
            self.engine.parents[rec['id']]=rec
        self.engine.journal=list(data.get('journal',[]))
        # Conservative epoch invalidation affects only the small parent
        # interreduction, never repeats the completed pair queue.
        self.engine.epochs=Counter({max(map(p.degree,r['row']),default=2):1
                                   for r in self.engine.parents if r['active']})
        with gzip.open(self.out/'search_archive.pkl.gz','rb') as stream:
            archive=pickle.load(stream)
        self.host_seen=dict(archive['checked_inputs'])
        self.engine.version=max(self.host_seen.values(),default=0)
        self.resolved_cancellations=archive.get('resolved_cancellations',set())
        self.exclusions=archive.get('exclusions',[])
        self.extension_examples=archive.get('reversal_examples',[])
        with gzip.open(self.out/'degree_queue.pkl.gz','rb') as stream:
            state=pickle.load(stream)
        for name,value in state.items():setattr(self,name,value)
        self.blocked=defaultdict(set,self.blocked)
        self.stats=Counter(summary['stats']);self.timings=Counter(summary['timings'])
        self.engine.stats=Counter(summary['reducer_stats']);self.rounds=list(summary['rounds'])
        for mon in set(self.host_seen)|set(self.blocked):self.register_input(mon)
        self.presentations_dirty=True;self.blocked_match_version=-1
        self.prior_seconds=summary.get('cumulative_construction_seconds',summary['seconds'])
        self.stage=dict(summary['stage']);self.window=self.stage['parent_degree']
        if self.current_pair is not None:
            item=self.current_pair;_,i,j,stamp=item
            # A pause can occur after marking a host seen but before matching
            # finishes. Reopen this one pair's hosts, retaining deduplicated S's.
            for _,a in self.engine.parent_patterns(self.engine.parents[i]):
                for _,z in self.engine.parent_patterns(self.engine.parents[j]):
                    for mon,_ in base.overlap_inputs(a,z,len(a[1])+len(z[1])):
                        self.host_seen.pop(mon,None)
            heapq.heappush(self.pair_heap,item);self.pair_scheduled.add(stamp)
            self.current_pair=None
        if self.current_task is not None:
            task=self.tasks[self.current_task]
            self.enqueue_task(self.current_task,task);self.current_task=None
        self.resumed=True
        self.report_options.update(resumed_saved_queue=True,
            prior_construction_seconds=self.prior_seconds,
            timing_scope='Cumulative active construction time; pause excluded; verification separate')
        self.timings['resume_loading_seconds']+=perf_counter()-tick
        self.start=perf_counter();self.next_progress=self.start+30

    def register_input(self,mon):
        if mon in self.registered_inputs:return
        self.registered_inputs.add(mon)
        for unit in set(mon):self.input_postings[unit].add(mon)

    def pair_stamp(self,i,j):
        a,z=self.engine.parents[i],self.engine.parents[j]
        return i,a['revision'],j,z['revision']

    def schedule_parent(self,pid):
        rec=self.engine.parents[pid]
        if not rec['active']:return
        for other in self.engine.parents:
            if not other['active']:continue
            i,j=max(pid,other['id']),min(pid,other['id'])
            stamp=self.pair_stamp(i,j)
            if stamp in self.pair_scheduled or stamp in self.pair_done:continue
            degree=max(max(map(p.degree,self.engine.parents[k]['row']),default=2) for k in (i,j))
            if degree>self.degree:continue
            heapq.heappush(self.pair_heap,(degree,i,j,stamp))
            self.pair_scheduled.add(stamp)

    def presentation_event(self,pid,kind):
        self.presentations_dirty=True
        self.schedule_parent(pid)
        self.stats['queued_parent_presentation_events']+=1

    def enqueue_task(self,key,task):
        if task['status']=='queued':return
        self.counter+=1;task['status']='queued';task['ticket']=self.counter
        degree=max(map(p.degree,task['current_row']),default=0)
        heapq.heappush(self.s_heap,(degree,self.counter,key))

    def check_host(self,mon,origin,force=False):
        self.control();self.register_input(mon)
        if not force and self.host_seen.get(mon)==self.engine.version:
            return self.engine.actions(mon)
        self.host_seen[mon]=self.engine.version
        self.stats['distinct_input_checks']+=1
        tick=perf_counter();actions=self.engine.actions(mon)
        self.timings['host_matching_seconds']+=perf_counter()-tick
        self.host_exposed[mon]=[pid for _,s in actions
                              for pid in s.get('equivalent_parent_ids',[s['parent']])]
        if len(actions)<2:return actions
        # Prefer the replacement with the smaller largest RHS term, as in
        # A->B2+C2 versus A->B1+C1 with B1 the largest remaining monomial.
        def tail_key(action):
            return tuple(sorted((b.mkey(m) for m in action[0] if m!=mon),reverse=True))
        first,source=min(actions,key=tail_key)
        fm=p.primitive(first)[0];fh=max(fm,key=b.mkey)
        for other,other_source in actions:
            if other==first:continue
            assert base.contextual_lms_match(mon,first,other)
            om=p.primitive(other)[0];oh=max(om,key=b.mkey)
            if p.quotient(mon,b.mono(fh+oh)) is not None:
                self.stats['disjoint_product_ambiguities_skipped']+=1;continue
            sp=p.subtract(first,first[mon],other,other[mon])
            if not sp:continue
            primitive,factor,scale=p.primitive(sp);key=p.encode(primitive)
            if key in self.tasks:
                self.stats['duplicate_S_polynomials_not_enqueued']+=1;continue
            proof={'overlap':origin,'common_input':mon,
                'left_identity':first,'right_identity':other,
                'left_source':source,'right_source':other_source,
                'S_polynomial':sp,'primitive_S_polynomial':primitive,
                'S_common_factor':factor,'S_coefficient_scale':scale}
            task={'proof':proof,'current_row':primitive,'steps':[],
                  'denominator':b.ONE,'status':'new'}
            self.tasks[key]=task;self.enqueue_task(key,task)
            self.stats['distinct_S_polynomials_enqueued']+=1
        return actions

    def process_pair(self,item):
        degree,i,j,stamp=item
        self.pair_scheduled.discard(stamp)
        if stamp!=self.pair_stamp(i,j) or not all(self.engine.parents[k]['active'] for k in (i,j)):
            self.stats['obsolete_pair_versions_skipped']+=1;return
        if stamp in self.pair_done:return
        self.current_pair=item
        self.stage={'parent_degree':self.window,'left_parent':i,'right_parent':j,
                    'phase':'minimal_overlaps'}
        self.stats['parent_pairs']+=1
        seen=set()
        for ti,a in self.engine.parent_patterns(self.engine.parents[i]):
            for tj,c in self.engine.parent_patterns(self.engine.parents[j]):
                tick=perf_counter()
                for mon,witness in base.overlap_inputs(a,c,len(a[1])+len(c[1])):
                    self.timings['input_generation_seconds']+=perf_counter()-tick
                    self.control()
                    if i==j and ti==tj and witness['shared_brackets']==len(a[1]):
                        self.stats['identical_occurrence_pairs_skipped']+=1
                    elif mon not in seen:
                        seen.add(mon)
                        self.stats['minimal_overlap_contexts_checked']+=1
                        self.stats['overlaps_above_parent_degree']+=int(p.degree(mon)>self.window)
                        self.check_host(mon,{'parents':[i,j],'terms':[ti,tj],**witness,'common_context':[]})
                    tick=perf_counter()
                self.timings['input_generation_seconds']+=perf_counter()-tick
        self.pair_done.add(stamp);self.current_pair=None

    def process_task(self,item):
        degree,ticket,key=item;task=self.tasks[key]
        if task['status']!='queued' or ticket!=task['ticket']:return
        self.current_task=key;task['status']='processing'
        self.stage={'parent_degree':self.window,'phase':'S_reduction',
                    'S_polynomial_degree':degree,'task':ticket}
        tick=perf_counter()
        try:
            result,den,steps=self.engine.reduce(task['current_row'],trace=True,
                                                degree_bound=self.degree)
        except base.AboveDegreeRemainder as stop:
            task['steps']+=stop.reduction_steps
            task['denominator']=b.pmul(task['denominator'],stop.denominator)
            task['current_row']=stop.partial_row
            task['status']='blocked';task['blocked_head']=stop.head
            self.blocked[stop.head].add(key);self.register_input(stop.head)
            self.stats['deferred_above_bound_reductions']+=1
            self.timings['S_reduction_seconds']+=perf_counter()-tick
            self.current_task=None;return
        task['steps']+=steps;task['denominator']=b.pmul(task['denominator'],den)
        row,factor,scale=p.primitive(result)
        while row and self.engine.candidate_term_actions(row):
            result,d2,more=self.engine.reduce(result,trace=True)
            if not more:raise RuntimeError('Primitive-only match requires explicit replay')
            task['steps']+=more;task['denominator']=b.pmul(task['denominator'],d2)
            row,factor,scale=p.primitive(result)
        self.timings['S_reduction_seconds']+=perf_counter()-tick
        self.stats['S_polynomials']+=1
        if not row:
            task['status']='zero';self.stats['zero_remainders']+=1
        elif max(map(p.degree,row))>self.degree:
            # Normally the first irreducible above-bound term is caught above.
            raise AssertionError('Above-bound result escaped early stop')
        elif hasattr(self,'retain_momentum_candidate') and not self.retain_momentum_candidate(row):
            task['status']='outside_momentum_window'
            task['current_row']=result
            self.stats['nonzero_remainders_outside_momentum_window']+=1
        else:
            proof={**task['proof'],'reduction_steps':task['steps'],
                   'denominator':task['denominator'],'removed_product':factor,
                   'removed_scale':scale,'all_terms_interreduced_without_groups':not getattr(self.engine,'potential_only_mode',False)}
            pid,new=self.engine.add_parent(row,proof)
            task['status']='retained';task['result_parent']=pid
            if new:self.stats['additional_parents']+=1
        self.current_task=None

    def cache_rechecks(self):
        """Exact product-divisibility indexing; no arbitrary contractions."""
        changed_heads=set()
        for head,records in list(self.engine.cache.items()):
            for row,source in records:
                identity=(head,p.encode(row))
                if identity not in self.known_cache_polynomials:
                    self.known_cache_polynomials.add(identity);changed_heads.add(head)
        affected=set()
        for head in changed_heads:
            if not head:continue
            unit=min(set(head),key=lambda u:len(self.input_postings.get(u,())))
            for mon in self.input_postings.get(unit,()):
                if p.quotient(mon,head) is not None:affected.add(mon)
        for mon in affected:
            for flag in (False,True):self.engine.action_cache.pop((self.engine.version,mon,flag),None)
        self.pending_host_checks.update(mon for mon in affected if mon in self.host_seen)
        self.stats['targeted_cached_replacement_inputs']+=len(affected)
        return affected

    def wake_blocked(self,heads=None):
        for head in list(self.blocked if heads is None else set(heads)&self.blocked.keys()):
            self.control()
            if not self.engine.actions(head,first_only=True):continue
            for key in self.blocked.pop(head):
                task=self.tasks[key]
                if task['status']=='blocked':
                    self.enqueue_task(key,task)
                    self.stats['deferred_reductions_reopened']+=1

    def stabilize(self,stage,allow_higher=False):
        self.window=stage
        while True:
            self.control()
            if self.s_heap and (allow_higher or self.s_heap[0][0]<=stage):
                self.process_task(heapq.heappop(self.s_heap));continue
            if self.pair_heap and self.pair_heap[0][0]<=stage:
                self.process_pair(heapq.heappop(self.pair_heap));continue
            if self.presentations_dirty:
                self.presentations_dirty=False
                tick=perf_counter();self.engine.interreduce()
                self.timings['backward_reduction_seconds']+=perf_counter()-tick
                continue
            affected=self.cache_rechecks()
            if self.pending_host_checks:
                heads=sorted(self.pending_host_checks,key=b.mkey)
                self.pending_host_checks.clear()
                for mon in heads:self.check_host(mon,{'targeted_cached_replacement_recheck':True},force=True)
                self.wake_blocked(affected);continue
            if self.blocked_match_version!=self.engine.version:
                self.blocked_match_version=self.engine.version
                self.wake_blocked();continue
            self.wake_blocked(affected)
            if self.s_heap and (allow_higher or self.s_heap[0][0]<=stage):continue
            return

    def checkpoint(self,status,stage,full=True):
        result=super().checkpoint(status,stage,full)
        if full and hasattr(self,'tasks'):
            tick=perf_counter()
            state={key:getattr(self,key) for key in ('pair_heap','pair_scheduled','pair_done',
                's_heap','tasks','blocked','counter','known_cache_polynomials',
                'pending_host_checks','current_pair','current_task')}
            with gzip.open(self.out/'degree_queue.pkl.gz','wb',compresslevel=1) as stream:
                pickle.dump(state,stream,protocol=5)
            self.timings['checkpoint_io_seconds']+=perf_counter()-tick
        if hasattr(self,'tasks'):
            elapsed=perf_counter()-self.start
            total=self.prior_seconds+elapsed
            result.update(seconds=elapsed,cumulative_construction_seconds=total,
                timings=dict(self.timings),
                queued_S_polynomials=sum(v['status']=='queued' for v in self.tasks.values()),
                deferred_above_bound_S_polynomials=sum(v['status']=='blocked' for v in self.tasks.values()),
                pending_parent_pairs=len(self.pair_heap),
                construction_compute_seconds=total-self.timings['checkpoint_io_seconds'])
            bp.save(self.out/'progress.json',result)
        return result

    def run(self):
        first_stage=self.window if self.resumed else 2
        if not self.resumed:
            self.window=2
            for parent in list(self.engine.parents):
                for ti,pattern in self.engine.parent_patterns(parent):
                    ll,bb,ee=pattern
                    for extra in base.matchings(ll,bb,ee):
                        for mon in b.normalize_graph(ll,bb,ee+extra):
                            self.check_host(mon,{'parent':parent['id'],'term':ti,'closure':extra})
        for stage in range(first_stage,self.degree+1):
            tick=perf_counter();self.stabilize(stage)
            self.rounds.append({'parent_degree':stage,'seconds':perf_counter()-tick,
                'active_parents':sum(r['active'] for r in self.engine.parents),
                'provisional_while_higher_S_polynomials_pending':True})
            self.checkpoint('provisional_degree_stage_finished',{'parent_degree':stage})
        self.stabilize(self.degree,allow_higher=True)
        # The allowed parent queue is now exhausted; high raw S-polynomials
        # were reduced as far as possible, retaining lower-degree remainders.
        for attempt in range(1,21):
            self.stage={'parent_degree':self.degree,'phase':'context_preparation','pass':attempt}
            version=self.engine.version;before=len(self.tasks)
            tick=perf_counter();self.prepare_contexts()
            self.timings['context_preparation_seconds']+=perf_counter()-tick
            self.stabilize(self.degree,allow_higher=True)
            if self.engine.version==version and len(self.tasks)==before:break
        else:raise RuntimeError('Context preparation did not stabilize in 20 passes')
        groups=[]
        for rec in self.engine.parents:
            if rec['active']:
                groups.append({'id':rec['id'],'family':rec['family'],'original':rec['raw'] is not None,
                    'group':prior.rule_group(rec['row']) if rec['row'] else 2,
                    'degree':max(map(p.degree,rec['row']),default=2)})
        bp.save(self.out/'final_groups.json',groups)
        return self.checkpoint('completed_degree_queue_and_encountered_contexts',
                               {'parent_degree':self.degree})


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=4)
    ap.add_argument('--seconds',type=float,default=0)
    ap.add_argument('--out',required=True)
    ap.add_argument('--resume',action='store_true')
    args=ap.parse_args();out=Path(args.out)
    if out.exists() and not args.resume:raise RuntimeError('Fresh output directory required')
    out.mkdir(parents=True,exist_ok=args.resume)
    task=DegreeQueueConstruction(args.particles,args.degree,out,args.seconds)
    if args.resume:
        task.restore_queue()
        (out/'resume_source.py').write_bytes(Path(__file__).read_bytes())
    else:(out/'construction_source.py').write_bytes(Path(__file__).read_bytes())
    bp.save(out/'process.json',{'pid':os.getpid(),'status':'running'})
    try:
        report=task.run();bp.save(out/'process.json',{'pid':os.getpid(),'status':report['status']})
    except BaseException as exc:
        status=('time_limit_partial' if isinstance(exc,TimeoutError) else
                'paused_partial' if isinstance(exc,(KeyboardInterrupt,InterruptedError)) else 'error_partial')
        task.checkpoint(status,task.stage)
        bp.save(out/'process.json',{'pid':os.getpid(),'status':status})
        (out/'error.txt').write_text(repr(exc)+'\n',encoding='utf-8')
        if not isinstance(exc,TimeoutError):raise


if __name__=='__main__':main()
