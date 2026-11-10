"""Full two-stage candidate interreduction, minimal parent overlaps only.

The amplitude reducer still performs group 1 then group 2 without a return.
Candidate identities are interreduced to a fixed point using complete 1->2
passes; any pass exposing a first-group match is recorded, not concealed.
No cache-version change requests another whole parent-pair pass. Actual
parent-presentation changes still use the original backward-check scheduling.
"""
import argparse
import json
import os
from pathlib import Path
from time import perf_counter
import strict_stages as base

b,bp,p=base.b,base.bp,base.p


class TwoStageReducer(base.StrictReducer):
    def actions(self,mon,first_only=False):
        # Roll back cache-driven global invalidation. Parent insertions and
        # presentation changes retain their ordinary version invalidation.
        return base.old.V32Reducer.actions(self,mon,first_only)

    def candidate_group_actions(self,row,group):
        # Candidate acceptance checks every available group, regardless of
        # the ancestry label carried by the candidate identity.
        return [(mon,actions[0]) for mon in sorted(row,key=b.mkey,reverse=True)
                if (actions:=self.actions(mon))]

    def reduce_candidate_group(self,row,group,degree_bound=None):
        pending,out,den,steps=dict(row),{},b.ONE,[]
        while pending:
            if hasattr(self,'budget_check'):self.budget_check()
            head=max(pending,key=b.mkey)
            actions=self.group_actions(head,group)
            if not actions:
                # Neither group can reduce this above-bound head. Do not
                # discard a term merely because it awaits the other group.
                if (degree_bound is not None and p.degree(head)>degree_bound
                        and not self.group_actions(head,3-group)):
                    self.stats['early_above_degree_stops']+=1
                    raise base.AboveDegreeRemainder(head,degree_bound,group,len(steps))
                b.add_term(out,head,pending.pop(head));continue
            rel,source=actions[0]
            assert max(rel,key=b.mkey)==head
            assert all(b.mkey(m)<b.mkey(head) for m in rel if m!=head)
            ah,rh=pending[head],rel[head]
            pending=p.subtract(pending,ah,rel,rh)
            if rh!=b.ONE:
                out=bp.poly_scale(out,rh);den=b.pmul(den,rh)
            steps.append({'input':head,'source':{**source,'origin_group':group},
                'identity':rel,'input_coefficient':ah,'leading_coefficient':rh,
                'stage':group,'top_behavior':base.ordering.top_behavior(rel)})
            if len(steps)>200000:raise RuntimeError('Reduction step limit')
        self.stats[f'candidate_group_{group}_steps']+=len(steps)
        return out,den,steps

    def reduce_candidate(self,row,group,degree_bound=None):
        result,den,steps=dict(row),b.ONE,[]
        for cycle in range(100):
            first,d1,t1=self.reduce_candidate_group(result,1,degree_bound)
            second,d2,t2=self.reduce_candidate_group(first,2,degree_bound)
            den=b.pmul(den,b.pmul(d1,d2));steps+=t1+t2
            if t1:group=1
            self.stats['candidate_complete_two_stage_passes']+=1
            again=any(self.group_actions(mon,1) for mon in second)
            if not again:
                return second,den,steps,group
            self.stats['candidate_passes_exposing_first_group']+=1
            result=second
        raise RuntimeError('Candidate interreduction did not terminate')

    def interreduce(self):
        updates=0
        while True:
            changed=False
            active=[r for r in self.parents if r['raw'] is None and r['active']]
            active.sort(key=lambda r:(max(map(p.degree,r['row'])),r['origin_group'],r['id']))
            for rec in active:
                if hasattr(self,'budget_check'):self.budget_check()
                row,group,pid=rec['row'],rec['origin_group'],rec['id']
                with self.without_parent(pid):
                    if not any(self.actions(mon) for mon in row):continue
                    result,den,steps,result_group=self.reduce_candidate(row,group)
                    normalized,factor,scale=p.primitive(result)
                    while normalized and any(self.actions(mon) for mon in normalized):
                        result,d2,more,result_group=self.reduce_candidate(result,result_group)
                        if not more:raise RuntimeError('Primitive match requires factor replay')
                        den=b.pmul(den,d2);steps+=more
                        normalized,factor,scale=p.primitive(result)
                    assert not any(self.actions(mon) for mon in normalized)
                self.replace_parent(pid,normalized,{'trigger_degree':max(map(p.degree,row)),
                    'reduction_steps':steps,'denominator':den,'removed_product':factor,
                    'removed_scale':scale,'interreduction_group':result_group,
                    'full_two_stage_interreduction':True})
                updates+=1;changed=True
            if not changed:return updates


def load_two_stage(data,archive_path=None):
    engine=base.load_strict(data,archive_path)
    engine.__class__=TwoStageReducer
    return engine


class TwoStageConstruction(base.StrictConstruction):
    def __init__(self,n,degree,out,seconds=15):
        super().__init__(n,degree,out,seconds)
        self.engine=TwoStageReducer(n,degree)
        self.engine.budget_check=self.control
        self.report_options.update(search_revision='full_two_stage_interreduction_minimal_overlaps',
            candidate_interreduction='Complete group-1 then group-2 passes to irreducibility; reentries recorded',
            pair_rescan_trigger='Changed parent presentations, not contextual-cache version changes',
            construction_limit_seconds=seconds)

    def run(self):
        self.window=2
        for parent in list(self.engine.parents):
            for ti,pattern in self.engine.parent_patterns(parent):
                ll,bb,ee=pattern
                for extra in base.matchings(ll,bb,ee):
                    for mon in b.normalize_graph(ll,bb,ee+extra):
                        self.check_host(mon,{'parent':parent['id'],'term':ti,'closure':extra})
        for window in range(2,self.degree+1):
            self.window=window
            for number in range(1,21):
                start=perf_counter();before=len(self.engine.parents)
                self.reset_overlap_checks();self.run_window(0)
                tick=perf_counter();changed=self.engine.interreduce()
                self.timings['backward_reduction_seconds']+=perf_counter()-tick
                self.rounds.append({'parent_degree':window,'round':number,
                    'insertions':len(self.engine.parents)-before,'presentation_updates':changed,
                    'active_parents':sum(r['active'] for r in self.engine.parents),
                    'seconds':perf_counter()-start})
                self.checkpoint('backward_pass_finished',{'parent_degree':window,'round':number})
                # Same stopping condition as the earlier fast construction.
                if not changed:break
            else:raise RuntimeError('No fixed point after 20 presentation passes')
            self.checkpoint('parent_stage_completed',{'parent_degree':window,'rounds':number})
        return self.checkpoint('completed_minimal_parent_queue',{'parent_degree':self.degree})


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=4)
    ap.add_argument('--seconds',type=float,default=15)
    ap.add_argument('--out',required=True)
    args=ap.parse_args();out=Path(args.out)
    if (out/'catalog.json').exists():raise RuntimeError('Fresh output directory required')
    task=TwoStageConstruction(args.particles,args.degree,out,args.seconds)
    out.mkdir(parents=True,exist_ok=True)
    (out/'construction_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'supporting_strict_stages.py').write_bytes(Path(base.__file__).read_bytes())
    bp.save(out/'process.json',{'pid':os.getpid(),'status':'running'})
    try:
        task.run();bp.save(out/'process.json',{'pid':os.getpid(),'status':'construction_finished'})
    except BaseException as exc:
        status=('time_limit_partial' if isinstance(exc,TimeoutError) else
                'paused_partial' if isinstance(exc,(KeyboardInterrupt,InterruptedError)) else 'error_partial')
        task.checkpoint(status,task.stage)
        bp.save(out/'process.json',{'pid':os.getpid(),'status':status})
        (out/'error.txt').write_text(repr(exc)+'\n',encoding='utf-8')
        if not isinstance(exc,TimeoutError):raise


if __name__=='__main__':main()
