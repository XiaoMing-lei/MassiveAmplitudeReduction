"""Incremental same-overlap route pools; no global overlap matching.

Only the two supplied parent placements are instantiated. Known routes are
joined to one reference as they arrive. Complete S-polynomials are reduced by
the existing group-independent reducer. Final groups are assigned afterward.
"""
import argparse
import gzip
import heapq
import json
import os
import pickle
from collections import defaultdict
from pathlib import Path
from time import perf_counter
import construct_degree_queue as old
import direct_tensor_overlaps as direct

b,bp,p,base=old.b,old.bp,old.p,old.base


class RoutePoolConstruction(old.DegreeQueueConstruction):
    def __init__(self,n,degree,out,seconds=0):
        super().__init__(n,degree,out,seconds)
        self.pools={};self.routes=[];self.route_edges=[]
        self.pools_by_parent=defaultdict(set);self.checks_by_parent=defaultdict(set)
        self.direct_cache={};self.context_examples=[]
        self.report_options.update(revision='incremental_route_pool',
            overlap_matching='Instantiate only the supplied parent embeddings',
            route_reference='Smallest largest RHS monomial; then remaining monomial support',
            overlap_catalog_search=False,
            cached_context_rechecks='Insert already known cached routes by exact product divisibility; no matching',
            timing_scope='Fresh construction, interreduction, context preparation and checkpoint I/O; verification separate')

    def check_host(self,*args,**kwargs):
        raise AssertionError('Global overlap matching is disabled in route-pool construction')

    @staticmethod
    def source_parents(source):
        parents=set(source.get('equivalent_parent_ids',[source['parent']]))
        for step in source.get('momentum_steps',[]):
            parents.update(RoutePoolConstruction.source_parents(step['source']))
        return parents

    def reset_task(self,key):
        task=self.tasks[key]
        if task['status']=='queued':return
        if task['status']=='blocked':
            head=task['blocked_head'];self.blocked[head].discard(key)
            if not self.blocked[head]:self.blocked.pop(head)
        task['current_row']=dict(task['proof']['primitive_S_polynomial'])
        task['steps']=[];task['denominator']=b.ONE
        self.enqueue_task(key,task)
        self.stats['dependent_S_polynomials_reopened']+=1

    def presentation_event(self,pid,kind):
        super().presentation_event(pid,kind)
        if kind!='update' or not hasattr(self,'pools_by_parent'):return
        # Reopen precisely the checks whose recorded reductions used this
        # presentation, and rebuild only pools containing its contextual routes.
        for key in self.checks_by_parent.get(pid,()):self.reset_task(key)
        for head in self.pools_by_parent.get(pid,()):
            pool=self.pools[head]
            valid={key:rid for key,rid in pool['routes'].items()
                   if all(self.engine.parents[k]['active'] and self.engine.parents[k]['revision']==rev
                          for k,rev in self.routes[rid]['presentation_versions'].items())}
            pool['routes']=valid;pool['reference']=None
            pool['epoch']+=1;pool['connections']=[]
            if not valid:continue
            tail=lambda rid:tuple(sorted((b.mkey(m) for m in self.routes[rid]['identity'] if m!=head),reverse=True))
            root=min(valid.values(),key=tail);pool['reference']=root
            for rid in valid.values():
                if rid!=root:self.queue_route_difference(head,root,rid,reopen=True)
            self.stats['pools_rebuilt_after_parent_update']+=1

    def process_task(self,item):
        super().process_task(item)
        task=self.tasks[item[2]]
        dependencies=set()
        for name in ('left_source','right_source'):dependencies.update(self.source_parents(task['proof'][name]))
        for step in task['steps']:dependencies.update(self.source_parents(step['source']))
        for pid in dependencies:self.checks_by_parent[pid].add(item[2])

    def register_route(self,head,row,source,origin):
        if not row or max(row,key=b.mkey)!=head:
            self.stats['rejected_nonleading_direct_routes']+=1;return None
        row=b.primitive(row)[0];encoding=p.encode(row)
        pool=self.pools.setdefault(head,{'routes':{},'reference':None,'epoch':0,'connections':[]})
        if encoding in pool['routes']:
            self.stats['duplicate_routes_reused']+=1;return pool['routes'][encoding]
        self.register_input(head)
        rid=len(self.routes)
        dependencies=self.source_parents(source)
        versions={pid:self.engine.parents[pid]['revision'] for pid in dependencies}
        self.routes.append({'id':rid,'head':head,'identity':row,'source':source,'origin':origin,
                            'presentation_versions':versions})
        for pid in dependencies:self.pools_by_parent[pid].add(head)
        pool['routes'][encoding]=rid;self.stats['distinct_contextual_routes']+=1
        reference=pool['reference']
        if reference is None:pool['reference']=rid
        else:
            self.queue_route_difference(head,reference,rid)
            def tail_key(index):
                return tuple(sorted((b.mkey(m) for m in self.routes[index]['identity'] if m!=head),reverse=True))
            if tail_key(rid)<tail_key(reference):
                pool['reference']=rid;self.stats['reference_changes']+=1
        primitive,factor,scale=p.primitive(row);h=max(primitive,key=b.mkey);key=p.encode(primitive)
        if key not in self.engine.cache_encodings[h]:
            saved_source={**source,'route_pool_record':rid,'removed_product':factor,
                          'coefficient_scale_removed':scale}
            self.engine.cache[h].append((primitive,saved_source))
            self.engine.cache_encodings[h].add(key)
            self.engine.stats['cached_contextual_replacements']+=1
            for flag in (False,True):self.engine.action_cache.pop((self.engine.version,h,flag),None)
        return rid

    def queue_route_difference(self,head,left_id,right_id,reopen=False):
        left,right=self.routes[left_id],self.routes[right_id]
        a,z=left['identity'],right['identity']
        assert base.contextual_lms_match(head,a,z)
        sp=p.subtract(a,a[head],z,z[head])
        pool=self.pools[head]
        edge={'common_input':head,'left_route':left_id,'right_route':right_id,'pool_epoch':pool['epoch'],
              'S_polynomial':sp,'actual_LMs_checked':True}
        pool['connections'].append(len(self.route_edges))
        self.route_edges.append(edge)
        if not sp:edge['status']='identically_zero';return
        primitive,factor,scale=p.primitive(sp);key=p.encode(primitive)
        edge['task_key']=key
        if key in self.tasks:
            if reopen:self.reset_task(key)
            edge['status']='existing_S_polynomial';self.stats['duplicate_S_polynomials_not_enqueued']+=1;return
        proof={'overlap':{'incremental_route_pool':True,'left_origin':left['origin'],
                         'right_origin':right['origin'],'route_edge':len(self.route_edges)-1},
            'common_input':head,'left_identity':a,'right_identity':z,
            'left_source':left['source'],'right_source':right['source'],
            'S_polynomial':sp,'primitive_S_polynomial':primitive,
            'S_common_factor':factor,'S_coefficient_scale':scale}
        task={'proof':proof,'current_row':primitive,'steps':[],
              'denominator':b.ONE,'status':'new'}
        self.tasks[key]=task;self.enqueue_task(key,task)
        edge['status']='enqueued';self.stats['distinct_S_polynomials_enqueued']+=1

    def direct_route(self,pid,ti,pattern,graph,placement,context_key):
        parent=self.engine.parents[pid];selected,mapping=placement
        key=(pid,parent['revision'],ti,context_key)
        if key in self.direct_cache:
            self.stats['direct_embedding_cache_hits']+=1;return self.direct_cache[key]
        tick=perf_counter();row=direct.attach(parent,pattern,graph,selected,mapping)
        self.timings['direct_identity_preparation_seconds']+=perf_counter()-tick
        self.stats['direct_identity_preparations']+=1
        source={'parent':pid,'parent_revision':parent['revision'],
                'kind':parent['family'] if parent['raw'] is not None else 'derived-context',
                'direct_embedding':True,'pattern_term':ti,'pattern':pattern,
                'common_graph':graph,'selected_edges':selected,'port_map':mapping}
        self.direct_cache[key]=(row,source)
        return row,source

    def process_pair(self,item):
        degree,i,j,stamp=item;self.pair_scheduled.discard(stamp)
        if stamp!=self.pair_stamp(i,j) or not all(self.engine.parents[k]['active'] for k in (i,j)):
            self.stats['obsolete_pair_versions_skipped']+=1;return
        if stamp in self.pair_done:return
        self.current_pair=item
        self.stage={'parent_degree':self.window,'left_parent':i,'right_parent':j,'phase':'direct_parent_overlaps'}
        self.stats['parent_pairs']+=1
        for ti,a in self.engine.parent_patterns(self.engine.parents[i]):
            for tj,z in self.engine.parent_patterns(self.engine.parents[j]):
                tick=perf_counter()
                for graph,shared,ap,zp,extra,keys in direct.overlap_frames(a,z):
                    self.timings['input_generation_seconds']+=perf_counter()-tick
                    self.control();self.stats['overlap_frames_after_dummy_relabel_dedup']+=1
                    origin={'parents':[i,j],'parent_versions':[stamp[1],stamp[3]],
                            'terms':[ti,tj],'shared_brackets':shared,
                            'common_graph':graph,'additional_contractions':extra}
                    # Normalize the common graph, without discarding its two
                    # placements. A prepared image need not have unit coefficient.
                    image=b.normalize_graph(*graph)
                    if image:
                        rows=[self.direct_route(i,ti,a,graph,ap,keys[0]),
                              self.direct_route(j,tj,z,graph,zp,keys[1])]
                        actual=[]
                        for row,source in rows:
                            head=max(row,key=b.mkey,default=None)
                            if head not in image:
                                self.stats['proposed_occurrence_not_actual_LM']+=1;actual.append(None);continue
                            rid=self.register_route(head,row,source,origin);actual.append(rid)
                        if all(r is not None for r in actual) and self.routes[actual[0]]['head']==self.routes[actual[1]]['head']:
                            self.stats['two_actual_LMs_in_supplied_pair']+=1
                    tick=perf_counter()
                self.timings['input_generation_seconds']+=perf_counter()-tick
        self.pair_done.add(stamp);self.current_pair=None

    def cache_rechecks(self):
        """Reuse known polynomials without asking for any other replacement.

        This also preserves factor-cancelled contextual applications discovered
        while reducing S's. It does not reconstruct them or search the catalog.
        """
        new=[]
        for head,records in list(self.engine.cache.items()):
            for row,source in list(records):
                key=(head,p.encode(row))
                if key not in self.known_cache_polynomials:
                    self.known_cache_polynomials.add(key);new.append((head,row,source))
        affected=set()
        for head,row,source in new:
            if not head:continue
            unit=min(set(head),key=lambda u:len(self.input_postings.get(u,())))
            for mon in list(self.input_postings.get(unit,())):
                rest=p.quotient(mon,head)
                if rest is None:continue
                affected.add(mon)
                for flag in (False,True):self.engine.action_cache.pop((self.engine.version,mon,flag),None)
                if mon in self.pools:
                    self.register_route(mon,p.multiply(row,rest),source,
                        {'known_cached_product':True,'cached_head':head,'untouched_factor':rest})
        self.stats['known_cached_routes_propagated']+=len(affected)
        return affected

    def prepare_contexts(self):
        # Match checks here concern final descendant retention, not an overlap
        # scan. Any alternatives already returned are inserted directly.
        records={}
        for head,entries in list(self.engine.cache.items()):
            if p.degree(head)>self.degree:continue
            for row,source in entries:
                if source['kind'] in ('M','derived-product'):continue
                records.setdefault(p.encode(row),(row,source))
        self.prepared=[];omitted=[]
        for key,(row,source) in records.items():
            self.control();head=max(row,key=b.mkey)
            available=self.engine.actions(head)
            for alternative,origin in available:
                self.register_route(head,alternative,origin,{'final_context_retention_check':True})
            def reference_key(action):
                primitive=p.primitive(action[0])[0]
                return p.degree(max(primitive,key=b.mkey)),p.encode(primitive)
            reference=min(available,key=reference_key) if available else (row,source)
            if p.encode(p.primitive(reference[0])[0])!=key:
                omitted.append({'source':source,'identity':row,'head_reduced_by':reference[1],
                                'reference_identity':reference[0]});continue
            tail={m:c for m,c in row.items() if m!=head}
            reduced,den,steps=self.engine.reduce(tail,trace=True,excluded_identities={key})
            b.add_term(reduced,head,b.pmul(row[head],den))
            prepared,factor,scale=p.primitive(reduced)
            assert prepared and max(prepared,key=b.mkey)==p.quotient(head,factor)
            self.prepared.append({'parent_source':source,'original_identity':row,
                'identity':prepared,'rhs_reduction_steps':steps,'denominator':den,
                'removed_product':factor,'removed_scale':scale,'group':old.prior.rule_group(prepared)})
        self.stats['encountered_contexts_for_preparation']=len(records)
        self.stats['omitted_reducible_contexts']=len(omitted)
        bp.save(self.out/'prepared_contexts.json',{'scope':'Encountered contexts of degree <= D',
            'retained':self.prepared,'omitted':omitted,'ordinary_M_applications_not_descendants':True})

    def checkpoint(self,status,stage,full=True):
        if full and hasattr(self,'pools'):
            tick=perf_counter()
            with gzip.open(self.out/'route_pool.pkl.gz','wb',compresslevel=1) as stream:
                pickle.dump({'pools':self.pools,'routes':self.routes,'edges':self.route_edges,
                    'pools_by_parent':self.pools_by_parent,'checks_by_parent':self.checks_by_parent},stream,protocol=5)
            self.timings['checkpoint_io_seconds']+=perf_counter()-tick
        return super().checkpoint(status,stage,full)

    def run(self):
        for stage in range(2,self.degree+1):
            tick=perf_counter();self.stabilize(stage)
            self.rounds.append({'parent_degree':stage,'seconds':perf_counter()-tick,
                'active_parents':sum(r['active'] for r in self.engine.parents),
                'provisional_while_higher_S_polynomials_pending':True})
            self.checkpoint('provisional_degree_stage_finished',{'parent_degree':stage})
        self.stabilize(self.degree,allow_higher=True)
        for attempt in range(1,21):
            self.stage={'parent_degree':self.degree,'phase':'context_preparation','pass':attempt}
            version=self.engine.version;before=len(self.tasks)
            tick=perf_counter();self.prepare_contexts()
            self.timings['context_preparation_seconds']+=perf_counter()-tick
            self.stabilize(self.degree,allow_higher=True)
            if self.engine.version==version and len(self.tasks)==before:break
        else:raise RuntimeError('Context preparation did not stabilize')
        bp.save(self.out/'final_groups.json',[{'id':r['id'],'family':r['family'],
            'original':r['raw'] is not None,'group':old.prior.rule_group(r['row']) if r['row'] else 2,
            'degree':max(map(p.degree,r['row']),default=2)} for r in self.engine.parents if r['active']])
        self.stats['overlap_pools']=len(self.pools);self.stats['route_connections']=len(self.route_edges)
        return self.checkpoint('completed_degree_queue_and_encountered_contexts',{'parent_degree':self.degree})


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--particles',type=int,default=3)
    ap.add_argument('--degree',type=int,default=4);ap.add_argument('--out',required=True)
    ap.add_argument('--seconds',type=float,default=0)
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=False)
    task=RoutePoolConstruction(args.particles,args.degree,out,args.seconds)
    for src in (Path(__file__),Path(direct.__file__)):(out/src.name).write_bytes(src.read_bytes())
    bp.save(out/'process.json',{'pid':os.getpid(),'status':'running'})
    try:
        report=task.run();bp.save(out/'process.json',{'pid':os.getpid(),'status':report['status']})
    except BaseException as exc:
        status='paused_partial' if isinstance(exc,(KeyboardInterrupt,InterruptedError)) else 'error_partial'
        task.checkpoint(status,task.stage);bp.save(out/'process.json',{'pid':os.getpid(),'status':status})
        (out/'error.txt').write_text(repr(exc),encoding='utf-8');raise


if __name__=='__main__':main()
