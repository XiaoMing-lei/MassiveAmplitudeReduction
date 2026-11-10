"""Save cached-route propagation between complete registrations.

Preserve the preselected rows, per-row input traversal and affected-input set.
Resume that continuation before processing any S tasks created within it.
The algebra, reference-route choices, order and cutoff remain unchanged.
"""
import heapq
from pathlib import Path
from time import perf_counter
import run_compact_queue as compact

c=compact.original.c


class ResumableOvernight(compact.CompactOvernight):
    entrypoint=str(Path(__file__).resolve())

    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.propagation_state=None

    def propagation_boundary(self):
        self.control()
        # These phases return directly to stabilize() on restore. The older
        # outer context-preparation loop has no serialized attempt cursor, so
        # retain its original whole-pass checkpoint boundary for now.
        if self.phase in ('degree_stages','above_bound_queue'):
            self.boundary()
        else:
            tick=perf_counter();self.disk_store.flush()
            self.timings['record_storage_seconds']+=perf_counter()-tick

    def cache_rechecks(self):
        state=self.propagation_state
        if state is None:
            new=[]
            for head,records in list(self.engine.cache.items()):
                for row,source in list(records):
                    key=(head,c.p.encode(row))
                    if key not in self.known_cache_polynomials:
                        self.known_cache_polynomials.add(key);new.append((head,row,source))
            # This pass registers routes only for existing pool heads, which
            # are already registered inputs. Hence postings cannot grow here.
            # Preserve their traversal order across Python set deserialization.
            postings={unit:tuple(values) for unit,values in self.input_postings.items()}
            state={'rows':new,'postings':postings,'row_index':0,'inputs':None,'input_index':0,
                   'affected':set(),'visited':0,'scanned':0}
            self.propagation_state=state
        while state['row_index']<len(state['rows']):
            head,row,source=state['rows'][state['row_index']]
            if not head:
                state['row_index']+=1;continue
            if state['inputs'] is None:
                unit=min(set(head),key=lambda u:len(state['postings'].get(u,())))
                state['inputs']=state['postings'].get(unit,())
                state['input_index']=0
            while state['input_index']<len(state['inputs']):
                mon=state['inputs'][state['input_index']]
                rest=c.p.quotient(mon,head)
                if rest is not None:
                    state['affected'].add(mon)
                    for flag in (False,True):
                        self.engine.action_cache.pop((self.engine.version,mon,flag),None)
                    if mon in self.pools:
                        self.register_route(mon,c.p.multiply(row,rest),source,
                            {'known_cached_product':True,'cached_head':head,'untouched_factor':rest})
                    state['visited']+=1
                # Advance only after a complete registration, before saving.
                state['input_index']+=1;state['scanned']+=1
                if ((rest is not None and state['visited']%128==0) or
                        state['scanned']%4096==0):
                    self.stage={'parent_degree':self.window,'phase':'cached_route_propagation',
                        'cached_source_index':state['row_index'],'cached_source_count':len(state['rows']),
                        'visited_divisible_inputs':state['visited'],
                        'input_index':state['input_index'],'input_count':len(state['inputs'])}
                    self.propagation_boundary()
            state['row_index']+=1;state['inputs']=None;state['input_index']=0
        affected=state['affected'];self.propagation_state=None
        tick=perf_counter();self.disk_store.flush()
        self.timings['record_storage_seconds']+=perf_counter()-tick
        self.stats['known_cached_routes_propagated']+=len(affected)
        return affected

    def stabilize(self,stage,allow_higher=False):
        self.window=stage
        while True:
            self.control()
            # An interrupted propagation must finish before its newly queued
            # S-polynomials or parent pairs can run, just as without a pause.
            if self.propagation_state is None:
                if self.s_heap and (allow_higher or self.s_heap[0][0]<=stage):
                    self.process_task(heapq.heappop(self.s_heap));continue
                if self.pair_heap and self.pair_heap[0][0]<=stage:
                    self.process_pair(heapq.heappop(self.pair_heap));continue
                if self.presentations_dirty:
                    self.presentations_dirty=False;tick=perf_counter();self.engine.interreduce()
                    self.timings['backward_reduction_seconds']+=perf_counter()-tick
                    continue
            affected=self.cache_rechecks()
            if self.pending_host_checks:
                heads=sorted(self.pending_host_checks,key=c.b.mkey)
                self.pending_host_checks.clear()
                for mon in heads:self.check_host(mon,{'targeted_cached_replacement_recheck':True},force=True)
                self.wake_blocked(affected);continue
            if self.blocked_match_version!=self.engine.version:
                self.blocked_match_version=self.engine.version;self.wake_blocked();continue
            self.wake_blocked(affected)
            if self.s_heap and (allow_higher or self.s_heap[0][0]<=stage):continue
            return

    def report(self,status):
        report=super().report(status)
        state=getattr(self,'propagation_state',None)
        report['resumable_propagation']=True
        report['propagation_checkpoint_phases']=['degree_stages','above_bound_queue']
        if state is not None:
            report['propagation_cursor']={key:state[key] for key in
                ('row_index','input_index','visited','scanned')}
            report['propagation_cursor']['rows']=len(state['rows'])
        return report


if __name__=='__main__':compact.main(runner_class=ResumableOvernight)
