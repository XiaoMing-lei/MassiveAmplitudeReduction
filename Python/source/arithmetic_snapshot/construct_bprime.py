"""Bounded tensor parent-overlap construction using the input-driven B' reducer.

The common-input degree bound is explicit. This deliberately does not claim the
unrestricted parent-LM cutoff completion whose coverage issue was set aside.
No external-spin profile or amplitude candidate list enters the constructor.
"""
from collections import Counter
from itertools import combinations
from functools import lru_cache
from pathlib import Path
from time import perf_counter
import argparse
import json

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p


def contextual_lms_match(common_input, left, right):
    """Both prepared contextual identities must actually lead on this input.

    An occurrence of an uncontracted potential LM is insufficient. Recheck the
    complete identities after their contractions and determinant preparation.
    A reversed orientation may be used only through its new actual LM.
    """
    return all(row and common_input in row and max(row, key=b.mkey) == common_input
               for row in (left, right))


def matchings(ll, bb, ee):
    used = {v for e in ee for v in e}
    color = {v:c for a,z,c in bb for v in (a,z)}
    free = tuple(v for v in range(len(ll)) if v not in used)
    def visit(remaining, eps):
        if not remaining:
            yield eps
            return
        a, rest = remaining[0], remaining[1:]
        yield from visit(rest, eps)
        for z in rest:
            if ll[a] == ll[z] and color[a] != color[z]:
                yield from visit(tuple(v for v in rest if v != z), eps+((a,z),))
    yield from visit(free, ())


def unions(left, right, bound):
    """Minimal unions: shared brackets and/or momentum-forming contractions."""
    al, ab, ae = left
    bl, bb, be = right
    minimum_shared = max(0, len(ab)+len(bb)-bound)
    edge_options = []
    for x,y,c in bb:
        edge_options.append([j for j,(a,z,cc) in enumerate(ab)
                             if c == cc and sorted((bl[x],bl[y])) == sorted((al[a],al[z]))])
    mapping = {}
    used = set()
    choices = []
    def visit(k, shared):
        if shared + len(bb)-k < minimum_shared:
            return
        if k == len(bb):
            ll = list(al); brackets = list(ab); sub = dict(mapping)
            for i, edge in enumerate(bb):
                if choices[i] is not None:
                    continue
                x,y,c = edge
                sub[x] = len(ll); ll.append(bl[x])
                sub[y] = len(ll); ll.append(bl[y])
                brackets.append((sub[x],sub[y],c))
            eps = list(ae)
            occupied = {a:z for a,z in eps} | {z:a for a,z in eps}
            for x,y in be:
                a,z = sub[x],sub[y]
                if a == z or (a in occupied and occupied[a] != z) or (z in occupied and occupied[z] != a):
                    return
                if a not in occupied:
                    eps.append((a,z)); occupied[a]=z; occupied[z]=a
            yield tuple(ll),tuple(brackets),tuple(eps),shared
            return
        x,y,c = bb[k]
        for j in edge_options[k]:
            if j in used:
                continue
            a,z,cc = ab[j]
            if al[a] != bl[x]:
                a,z=z,a
            mapping[x],mapping[y]=a,z
            used.add(j); choices.append(j)
            yield from visit(k+1,shared+1)
            choices.pop(); used.remove(j)
            del mapping[x]; del mapping[y]
        if len(ab)+len(bb)-shared <= bound or shared+len(bb)-k-1 >= minimum_shared:
            choices.append(None)
            yield from visit(k+1,shared)
            choices.pop()
    yield from visit(0,0)


def overlap_inputs(left, right, bound):
    seen = set()
    for ll,bb,ee,shared in unions(left,right,bound):
        if len(bb)>bound:
            continue
        for extra in matchings(ll,bb,ee):
            if not shared and not extra:
                continue
            # Structural normalization precedes substitution of the identities.
            prepared=b.normalize_graph(ll,bb,ee+extra)
            for mon in prepared:
                if p.degree(mon)>bound or mon in seen:
                    continue
                seen.add(mon)
                yield mon, {'shared_brackets':shared,'labels':ll,'brackets':bb,
                            'inherited_contractions':ee,'additional_contractions':extra,
                            'prepared_common_image':prepared}


@lru_cache(None)
def necessary_repeated_slots(mon,parent_labels):
    """Slots that must be touched to expose a currently vanishing Schouten.

    If an occurrence retains an untouched pair of equal-particle free indices,
    physical symmetrization kills that occurrence. Any context exposing it must
    attach an opposite-chirality bracket to one of this pair. For each possible
    occurrence choose one such pair, then take their union. If an occurrence
    has no such pair, no restriction is justified.
    """
    color,*labels=parent_labels
    repeated=sorted(i for i,k in Counter(labels).items() if k==2)
    if not repeated:return ()
    ll,bb,ee=b.graph(mon)
    occupied={v for e in ee for v in e}
    needed=set();found=False
    for a,z in combinations(range(len(bb)),2):
        if bb[a][2]!=color or bb[z][2]!=color:continue
        ports=bb[a][:2]+bb[z][:2]
        if sorted(ll[v] for v in ports)!=labels:continue
        found=True
        free_pairs=[tuple(v for v in ports if ll[v]==i)
                    for i in repeated
                    if all(v not in occupied for v in ports if ll[v]==i)]
        if not free_pairs:return ()
        needed.update(free_pairs[0])
    return tuple(sorted(needed)) if found else ()


@lru_cache(None)
def external_children(mon,n,required=()):
    ll,bb,ee=b.graph(mon)
    occupied={v for e in ee for v in e}
    color={v:c for a,z,c in bb for v in (a,z)}
    free=[v for v in range(len(ll)) if v not in occupied]
    result={}
    for i,j in combinations(range(1,n+1),2):
        for c in (0,1):
            aa=[None]+[v for v in free if ll[v]==i and color[v]!=c]
            zz=[None]+[v for v in free if ll[v]==j and color[v]!=c]
            for a in aa:
                for z in zz:
                    if a is None and z is None:continue
                    if required and a not in required and z not in required:continue
                    off=len(ll)
                    eps=ee+tuple((v,off+k) for k,v in enumerate((a,z)) if v is not None)
                    for out in b.normalize_graph(ll+(i,j),bb+((off,off+1,c),),eps):
                        result.setdefault(out,{'attach':[i,j,c,a,z]})
    return tuple(result.items())


class Construction:
    def __init__(self,n,degree,seconds=0,tag=''):
        bp.configure(n,degree)
        self.engine=bp.Reducer(n,degree)
        self.n=n;self.degree=degree;self.seconds=seconds
        self.start=perf_counter();self.stats=Counter();self.timings=Counter()
        self.host_seen={};self.host_proofs=[]
        self.host_exposed={}
        self.host_branches={}
        self.resolved_cancellations=set()
        self.out=Path(__file__).parent/'bprime'/(f'n{n}_d{degree}'+tag)
        self.last_save=self.start
        self.last_progress=self.start
        self.resume_stage=0
        self.resume_right=0
        self.prior_seconds=0
        self.stage={'left_parent':0,'right_parent':0}
        self.first_window=min(4,degree)
        self.window=degree

    def restore(self,path):
        data=json.loads(Path(path).read_text())
        if data.get('runtime_only'):
            raise ValueError('Resume from the full construction checkpoint, not the smaller application cache.')
        for rec in data['parents']:
            if rec['raw'] is None:
                self.engine.add_parent(bp.read_row(rec['row']),{**rec['source'],'catalog_namespace':str(path)})
        # These are contexts already requested by B', not an enumerated A table.
        # Restore them with hash deduplication; never use quadratic list scans.
        if len(self.engine.parents)==len(data['parents']):
            for rec in data.get('descendants',[]):
                h=bp.freeze(rec['head']);row=bp.read_row(rec['identity']);key=p.encode(row)
                if key not in self.engine.cache_encodings[h]:
                    self.engine.cache[h].append((row,rec['source']))
                    self.engine.cache_encodings[h].add(key)
        self.resume_stage=data['summary']['stage'].get('left_parent',0)
        self.resume_right=data['summary']['stage'].get('right_parent',0)
        self.prior_seconds=data['summary']['seconds']+data['summary'].get('prior_seconds',0)
        self.resolved_cancellations.update(bp.freeze(k) for k in data.get('resolved_cancellations',[]))
        for mon,version in data.get('checked_inputs',[]):
            self.host_seen[bp.freeze(mon)]=version
        for mon,parents in data.get('checked_parent_occurrences',[]):
            self.host_exposed[bp.freeze(mon)]=parents
        for rec in self.engine.parents:
            if rec['raw'] is None and rec['source'] and 'S_polynomial' in rec['source']:
                raw=rec['source']['S_polynomial']
                row=bp.read_row(raw) if isinstance(raw,list) else raw
                self.resolved_cancellations.add(p.encode(p.primitive(row)[0]))
        if data['summary']['status']=='completed_bounded_parent_overlap_queue' and data['summary']['degree']<self.degree:
            self.first_window=data['summary']['degree']+1
            self.resume_stage=0
            self.resume_right=0
        else:
            self.first_window=data['summary']['stage'].get('window',self.degree)

    def checkpoint(self,status,stage,full=True):
        tick=perf_counter()
        report={'particles':self.n,'degree':self.degree,'status':status,'stage':stage,
                'seconds':perf_counter()-self.start,'parents':len(self.engine.parents),
                'prior_seconds':self.prior_seconds,
                'originals':self.n**2+2*(self.n*(self.n-1)*(self.n-2)//2+self.n*(self.n-1)//2+
                                      (self.n*(self.n-1)*(self.n-2)*(self.n-3)//24)),
                'parent_degrees':dict(Counter(max(map(p.degree,x['row']),default=2)
                                      for x in self.engine.parents)),
                'stats':dict(self.stats),'reducer_stats':dict(self.engine.stats),
                'known_overlap_inputs_including_restored':len(self.host_seen),
                'timings':dict(self.timings),
                'scope':'Minimal parent unions with shared brackets and all admissible free-port cross/closure matchings; common input degree bounded. Not arbitrary extra spectator closure.',
                'no_basis_enumeration':True,'no_component_construction':True}
        bp.save(self.out/'progress.json',report)
        if full:bp.save(self.out/'catalog.json',{'summary':report,'parents':self.engine.parents,
                  'checked_inputs':list(self.host_seen.items()),
                  'checked_parent_occurrences':list(self.host_exposed.items()),
                  'resolved_cancellations':list(self.resolved_cancellations),
                  'descendants':[{'head':h,'identity':row,'source':source}
                                 for h,records in self.engine.cache.items() for row,source in records]})
        self.last_progress=perf_counter()
        if full:self.last_save=self.last_progress
        self.timings['checkpoint_io_seconds']+=perf_counter()-tick
        print(json.dumps({k:report[k] for k in ('status','stage','seconds','parents','stats')}),flush=True)
        return report

    def check_host(self,mon,origin):
        previous=self.host_seen.get(mon)
        if previous is not None and previous!=self.engine.version and mon in self.host_exposed:
            if not self.engine.matching_may_have_changed(mon,previous):
                self.host_seen[mon]=self.engine.version
                self.stats['unaffected_overlap_checks_reused']+=1
        if self.host_seen.get(mon)==self.engine.version:
            if mon in self.host_exposed:
                return [({}, {'parent':pid}) for pid in self.host_exposed[mon]]
            return self.engine.actions(mon)
        self.host_seen[mon]=self.engine.version
        self.stats['distinct_input_checks']+=1
        tick=perf_counter()
        actions=self.engine.actions(mon)
        self.host_exposed[mon]=[pid for row,source in actions
                               for pid in source.get('equivalent_parent_ids',[source.get('parent')])]
        self.timings['matching_seconds']+=perf_counter()-tick
        if len(actions)<2:
            return actions
        if mon not in self.host_branches:
            first,source=actions[0]
            self.host_branches[mon]=(first,source,{p.encode(first)})
        first,source,checked=self.host_branches[mon]
        first_primitive = None
        for other,other_source in actions:
            encoding=p.encode(other)
            if encoding in checked:continue
            checked.add(encoding)
            # Recheck the two actual occurrences immediately before preparing
            # a cancellation. Do not rely only on parent IDs being present or
            # on their uncontracted LM/potential-LM labels.
            if not contextual_lms_match(mon, first, other):
                self.stats['rejected_nonleading_contextual_cancellations']+=1
                continue
            if first_primitive is None:
                first_primitive=p.primitive(first)[0]
                first_head=max(first_primitive,key=b.mkey)
            other_primitive=p.primitive(other)[0]
            other_head=max(other_primitive,key=b.mkey)
            # Independent replacements on untouched tensor-product factors
            # commute. This does not cancel or ignore a contraction edge.
            if p.quotient(mon,b.mono(first_head+other_head)) is not None:
                self.stats['disjoint_product_ambiguities_skipped']+=1
                continue
            sp=p.subtract(first,first[mon],other,other[mon])
            if not sp:
                continue
            primitive_sp,sp_factor,sp_scale=p.primitive(sp)
            sp_key=p.encode(primitive_sp)
            if sp_key in self.resolved_cancellations:
                self.stats['repeated_factor_multiples_skipped']+=1
                continue
            tick=perf_counter()
            remainder,den,steps=self.engine.reduce(primitive_sp,trace=True)
            self.timings['S_reduction_seconds']+=perf_counter()-tick
            self.stats['S_polynomials']+=1
            if not remainder:
                self.stats['zero_remainders']+=1
                self.resolved_cancellations.add(sp_key)
                continue
            row,factor,scale=p.primitive(remainder)
            # Normalization/factor removal is followed by a term-by-term check.
            # Do not register a partially reduced identity. The current reducer
            # visits every term; this gate also catches a future matcher/cache
            # regression or a reduction exposed only by primitive preparation.
            remaining_actions=self.engine.candidate_term_actions(row)
            if remaining_actions:
                raise RuntimeError('Generated identity still has reducible terms after '
                                   'primitive preparation; no new parent registered.')
            if max(map(p.degree,row))>self.degree:
                self.stats['over_degree_remainders']+=1
                continue
            certificate={'overlap':origin,'common_input':mon,
                         'left_identity':first,'right_identity':other,
                         'left_source':source,'right_source':other_source,
                         'S_polynomial':sp,'reduction_steps':steps,
                         'primitive_S_polynomial':primitive_sp,'S_common_factor':sp_factor,
                         'S_coefficient_scale':sp_scale,
                         'denominator':den,'removed_product':factor,'removed_scale':scale}
            certificate['all_terms_irreducible_before_registration']=True
            pid,new=self.engine.add_parent(row,certificate)
            if new:
                self.stats['additional_parents']+=1
                print(f'parent {pid}: degree {max(map(p.degree,row))}, terms {len(row)}, {perf_counter()-self.start:.3f}s',flush=True)
            self.resolved_cancellations.add(sp_key)
        return actions

    def contextual_overlap(self,mon,origin,pair,seen):
        todo=[(mon,[])]
        while todo:
            host,path=todo.pop()
            if host in seen:continue
            seen.add(host)
            actions=self.check_host(host,{**origin,'common_context':path})
            actual=[pid for r,s in actions
                    for pid in s.get('equivalent_parent_ids',[s.get('parent')])]
            exposed=(all(x in actual for x in pair) if pair[0]!=pair[1]
                     else actual.count(pair[0])>=2)
            # A resolved cancellation ends this branch. Unexposed potential
            # overlaps need their shared external context, one bracket at a time.
            if not exposed and p.degree(host)<self.window:
                required=()
                for pid in pair:
                    parent=self.engine.parents[pid]
                    if pid not in actual and parent['family']=='S':
                        candidate=necessary_repeated_slots(host,tuple(parent['labels']))
                        if candidate and (not required or len(candidate)<len(required)):
                            required=candidate
                if required:self.stats['repeated_slot_context_restrictions']+=1
                for child,attachment in external_children(host,self.n,required):
                    if child not in seen and p.degree(child)<=self.window:
                        todo.append((child,path+[attachment]))
            if perf_counter()-self.last_progress>30:
                self.checkpoint('running',self.stage,full=perf_counter()-self.last_save>120)
            if self.seconds and perf_counter()-self.start>self.seconds:
                raise TimeoutError('Saved finite-window partial checkpoint.')

    def run(self):
        # First include intrinsic closures, especially the diagonal momentums.
        for parent in list(self.engine.parents):
            if parent['raw'] is None:continue
            for ti,pattern in self.engine.parent_patterns(parent):
                ll,bb,ee=pattern
                for extra in matchings(ll,bb,ee):
                    for mon in b.normalize_graph(ll,bb,ee+extra):
                        self.check_host(mon,{'parent':parent['id'],'term':ti,'closure':extra})
        for window in range(self.first_window,self.degree+1):
            self.window=window
            self.run_window(self.resume_stage if window==self.first_window else 0,
                            self.resume_right if window==self.first_window else 0)
            self.checkpoint('window_completed' if window<self.degree else 'completed_bounded_parent_overlap_queue',
                            {'window':window,'parents_processed':len(self.engine.parents)})
        return self.checkpoint('completed_bounded_parent_overlap_queue',{'window':self.degree,'parents_processed':len(self.engine.parents)})

    def run_window(self,start,right_start=0):
        # Complete the lower window before allowing higher-degree overlaps.
        i=start
        while i<len(self.engine.parents):
            left=self.engine.parents[i]
            lp=list(self.engine.parent_patterns(left))
            for j in range(right_start if i==start else 0,i+1):
                self.stage={'window':self.window,'left_parent':i,'right_parent':j}
                right=self.engine.parents[j]
                rp=list(self.engine.parent_patterns(right))
                self.stats['parent_pairs']+=1
                pair_seen=set()
                for ti,a in lp:
                    for tj,c in rp:
                        tick=perf_counter()
                        for mon,witness in overlap_inputs(a,c,self.window):
                            self.timings['input_generation_seconds']+=perf_counter()-tick
                            if i==j and ti==tj and witness['shared_brackets']==len(a[1]):
                                self.stats['identical_occurrence_pairs_skipped']+=1
                                tick=perf_counter()
                                continue
                            if mon not in pair_seen:
                                self.contextual_overlap(mon,{'parents':[i,j],'terms':[ti,tj],**witness},(i,j),pair_seen)
                            tick=perf_counter()
                        self.timings['input_generation_seconds']+=perf_counter()-tick
                if perf_counter()-self.last_progress>30:
                    self.checkpoint('running',self.stage,full=perf_counter()-self.last_save>120)
                if self.seconds and perf_counter()-self.start>self.seconds:
                    raise TimeoutError('Saved finite-window partial checkpoint.')
            i+=1


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=4)
    ap.add_argument('--seconds',type=float,default=0)
    ap.add_argument('--tag',default='')
    ap.add_argument('--resume')
    args=ap.parse_args()
    task=Construction(args.particles,args.degree,args.seconds,args.tag)
    if args.resume:task.restore(args.resume)
    try:task.run()
    except TimeoutError:task.checkpoint('time_limit_partial',task.stage)


if __name__=='__main__':main()
