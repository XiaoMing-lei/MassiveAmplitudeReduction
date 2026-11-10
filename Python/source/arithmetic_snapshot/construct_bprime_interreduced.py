"""Degree-staged B' completion with versioned backward reduction.

Uses the existing bounded parent-union construction. No amplitude candidates or
bases are enumerated. Old catalogs and proofs are never overwritten.
"""
import argparse
from collections import Counter,defaultdict
from contextlib import contextmanager
from pathlib import Path
from time import perf_counter
import json
import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_bprime import Construction,matchings


class VersionedReducer(bp.Reducer):
    def __init__(self,n,degree,unique_momentum_lm=False):
        super().__init__(n,degree,unique_momentum_lm=unique_momentum_lm)
        self.epochs=Counter();self.journal=[]
        for rec in self.parents:rec.update(active=True,revision=0,verified_epochs={})
        self.epochs[2]=1

    def add_parent(self,row,source):
        pid,new=super().add_parent(row,source)
        if new:
            rec=self.parents[pid];d=max(map(p.degree,rec['row']))
            self.epochs[d]+=1
            rec.update(active=True,revision=0,initial_row=dict(rec['row']),
                       verified_epochs=dict(self.epochs),updates=[])
            self.journal.append({'event':'insert','parent':pid,'revision':0,
                                 'row':dict(rec['row']),'source':source})
        return pid,new

    def actions(self,mon,first_only=False):
        result=super().actions(mon,first_only)
        return [(row,{**source,'parent_revision':self.parents[source['parent']]['revision']})
                for row,source in result]

    @contextmanager
    def without_parent(self,pid):
        saved=(self.cache,self.cache_encodings,self.action_cache,self.derived_patterns)
        self.cache=defaultdict(list,{h:[(r,s) for r,s in entries if s['parent']!=pid]
                                    for h,entries in self.cache.items()})
        self.cache_encodings=defaultdict(set,{h:{p.encode(r) for r,s in entries}
                                             for h,entries in self.cache.items()})
        self.action_cache={}
        self.derived_patterns=[entry for entry in self.derived_patterns if entry[0]!=pid]
        try:yield
        finally:self.cache,self.cache_encodings,self.action_cache,self.derived_patterns=saved

    def replace_parent(self,pid,row,proof):
        rec=self.parents[pid];old=rec['row'];old_d=max(map(p.degree,old))
        rec['revision']+=1;rec['row']=row;rec['active']=bool(row)
        proof={**proof,'parent':pid,'revision':rec['revision'],'old_row':old,'row':row}
        rec['updates'].append(proof);self.journal.append({'event':'update',**proof})
        self.epochs[old_d]+=1
        if row:
            new_d=max(map(p.degree,row))
            if new_d!=old_d:self.epochs[new_d]+=1
        self.version+=1
        # A changed identity invalidates its contextual presentations. Rebuild
        # the small derived index and discard application caches conservatively.
        self.derived_patterns=[];self.cache=defaultdict(list);self.cache_encodings=defaultdict(set)
        self.action_cache={};self.derived_context_cache={}
        for parent in self.parents:
            if parent['raw'] is not None or not parent['active']:continue
            for ti,pattern in self.parent_patterns(parent):
                ll,bb,ee=pattern
                signature=Counter((c,tuple(sorted((ll[a],ll[z])))) for a,z,c in bb)
                self.derived_patterns.append((parent['id'],ti,pattern,signature))
            head=max(parent['row'],key=b.mkey)
            self.cache[head].append((parent['row'],{'parent':parent['id'],'kind':'derived-product'}))
            self.cache_encodings[head].add(p.encode(parent['row']))
        rec['verified_epochs']=dict(self.epochs)

    def matching_may_have_changed(self,mon,previous_version):
        # Insertion stamps and presentation revisions share this version space.
        return previous_version!=self.version

    def interreduce(self):
        updates=0;stats=Counter()
        while True:
            changed=False
            active=[r for r in self.parents if r['raw'] is None and r['active']]
            active.sort(key=lambda r:(max(map(p.degree,r['row'])),r['id']))
            for rec in active:
                if hasattr(self,'budget_check'):self.budget_check()
                row=rec['row'];degree=max(map(p.degree,row));pid=rec['id']
                dirty=[d for d,v in self.epochs.items() if d<=degree and
                       rec['verified_epochs'].get(d,0)!=v]
                if not dirty:
                    stats['unchanged_degree_epochs_skipped']+=1;continue
                threshold=min(dirty)
                # Equal-degree insertions only revisit top-degree potential
                # terms. Lower terms are reopened only after lower-degree rules
                # have actually changed (including new low-degree remainders).
                candidates=[m for m in row if p.degree(m)>=threshold]
                stats['potential_terms_examined']+=sum(p.degree(m)==degree for m in candidates)
                stats['lower_terms_reopened']+=sum(p.degree(m)<degree for m in candidates)
                with self.without_parent(pid):
                    reducible=next((m for m in sorted(candidates,key=b.mkey,reverse=True)
                                    if self.actions(m,first_only=True)),None)
                    if reducible is None:
                        rec['verified_epochs']=dict(self.epochs);continue
                    result,den,steps=self.reduce(row,trace=True)
                    normalized,factor,scale=p.primitive(result)
                    assert not self.candidate_term_actions(normalized)
                self.replace_parent(pid,normalized,{'trigger_degree':threshold,
                    'reduction_steps':steps,'denominator':den,'removed_product':factor,
                    'removed_scale':scale})
                updates+=1;changed=True
            if not changed:break
        self.stats.update(stats)
        return updates


class InterreducedConstruction(Construction):
    def __init__(self,n,degree,seconds=600,tag='_interreduced'):
        super().__init__(n,degree,seconds,tag)
        self.engine=VersionedReducer(n,degree);self.first_window=2;self.rounds=[]

    def checkpoint(self,status,stage,full=True):
        active=[r for r in self.engine.parents if r['active']]
        report={'particles':self.n,'degree':self.degree,'status':status,'stage':stage,
                'seconds':perf_counter()-self.start,'parents':len(active),
                'historical_parent_records':len(self.engine.parents),
                'originals':sum(r['raw'] is not None for r in active),
                'parent_degrees':dict(Counter(max(map(p.degree,r['row']),default=2) for r in active)),
                'stats':dict(self.stats),'reducer_stats':dict(self.engine.stats),'rounds':self.rounds,
                'timings':dict(self.timings),'no_basis_enumeration':True,
                'scope':'Existing bounded parent unions and unresolved shared contexts; common input degree bounded. Versioned backward reduction and repeated overlap passes. Not arbitrary additional-context closure.'}
        report.update(getattr(self, 'report_options', {}))
        bp.save(self.out/'progress.json',report)
        if full:
            bp.save(self.out/'catalog.json',{'summary':report,'parents':active,
                    'history_records':self.engine.parents,'journal':self.engine.journal,
                    'descendants':[{'head':h,'identity':r,'source':s}
                         for h,items in self.engine.cache.items() for r,s in items]})
        self.last_progress=perf_counter()
        if full:self.last_save=self.last_progress
        print(json.dumps({k:report[k] for k in ('status','stage','seconds','parents')}),flush=True)
        return report

    def reset_overlap_checks(self):
        self.host_seen={};self.host_exposed={};self.host_branches={}
        self.resolved_cancellations=set()

    def run(self):
        for parent in list(self.engine.parents):
            for ti,pattern in self.engine.parent_patterns(parent):
                ll,bb,ee=pattern
                for extra in matchings(ll,bb,ee):
                    for mon in b.normalize_graph(ll,bb,ee+extra):
                        self.check_host(mon,{'parent':parent['id'],'term':ti,'closure':extra})
        for window in range(2,self.degree+1):
            self.window=window;round_number=0
            while True:
                round_number+=1;start=perf_counter();before=len(self.engine.parents)
                self.reset_overlap_checks()
                self.run_window(0)
                tick=perf_counter();changed=self.engine.interreduce()
                self.timings['backward_reduction_seconds']+=perf_counter()-tick
                self.rounds.append({'window':window,'round':round_number,
                    'insertions':len(self.engine.parents)-before,'presentation_updates':changed,
                    'active_parents':sum(r['active'] for r in self.engine.parents),
                    'seconds':perf_counter()-start})
                self.checkpoint('backward_pass_finished',{'window':window,'round':round_number})
                if not changed:break
                if round_number>=20:raise RuntimeError('No fixed point after 20 rounds; checkpoint preserved.')
            self.checkpoint('window_completed',{'window':window,'rounds':round_number})
        return self.checkpoint('completed_bounded_interreduced_queue',{'window':self.degree})


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=4);ap.add_argument('--seconds',type=float,default=600)
    ap.add_argument('--tag',default='_interreduced');a=ap.parse_args()
    task=InterreducedConstruction(a.particles,a.degree,a.seconds,a.tag)
    try:task.run()
    except TimeoutError:task.checkpoint('time_limit_partial',task.stage)


if __name__=='__main__':main()
