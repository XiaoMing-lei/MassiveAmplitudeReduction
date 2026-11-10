"""Exact contextual matching optimization, isolated from the running worker.

No change to allowed embeddings, physical symmetrization, order, or B2 overlaps.
Identity rows are immutable after insertion; revision changes replace the row.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, permutations, product

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from efficient_b2_restart import BoundedCache, EfficientReducer, EfficientB2


_original_graph=b.graph
_original_details=bp.graph_details
_original_mkey=b.mkey


@lru_cache(maxsize=50000)
def graph(mon):
    return _original_graph(mon)


@lru_cache(maxsize=20000)
def graph_details(mon):
    return _original_details(mon)


@lru_cache(maxsize=20000)
def unit_key(unit):
    return bp.unit_key(unit)


@lru_cache(maxsize=50000)
def mkey(mon):
    bound=b.ORDER_BOUND
    hist=[0]*(bound+1)
    traces=[0]*(bound+1)
    fillings=[[] for _ in range(bound+1)]
    degree=0
    for unit in mon:
        d=unit[0];degree+=d
        if 1<=d<=bound:
            hist[d]+=1
            traces[d]-=bool(unit[1])
            fillings[d].append(unit_key(unit))
    return (degree,tuple(hist[:0:-1]),tuple(traces[:0:-1]),
            tuple(tuple(sorted(values)) for values in fillings[:0:-1]))


def install_primitives():
    # configure() clears b.mkey whenever ORDER_BOUND changes. Keep the same
    # interface and clear here too when switching implementations in tests.
    mkey.cache_clear()
    b.graph=graph
    bp.graph_details=graph_details
    b.mkey=mkey


def prepared_terms(row):
    result=[]
    for mon,coefficient in row.items():
        labels,brackets,eps=b.graph(mon)
        used={v for edge in eps for v in edge}
        free=defaultdict(list)
        for v,label in enumerate(labels):
            if v not in used:free[label].append(v)
        result.append((coefficient,labels,brackets,eps,dict(free)))
    degree=max((len(term[2]) for term in result),default=0)
    return ([term for term in result if len(term[2])==degree],
            [term for term in result if len(term[2])<degree])


def embed_prepared(terms,pattern,mon,selected,mapping,stats):
    # Same physical symmetrization and signs as bp.embed_physical. First
    # evaluate every highest-degree source term, including their cancellations.
    ll,bb,ee=b.graph(mon)
    internal={frozenset((mapping[a],mapping[z])) for a,z in pattern[2]}
    remaining_bb=tuple(edge for i,edge in enumerate(bb) if i not in selected)
    selected_ports={v for i in selected for v in bb[i][:2]}
    context_ee=tuple(edge for edge in ee if frozenset(edge) not in internal)
    holes=sorted({v for edge in context_ee for v in edge if v in selected_ports})
    if any(a in selected_ports and z in selected_ports for a,z in context_ee):
        return {}
    hole_groups=defaultdict(list)
    for v in holes:hole_groups[ll[v]].append(v)
    external=sorted({v for edge in remaining_bb for v in edge[:2]})
    ext_map={v:i for i,v in enumerate(external)}
    ext_labels=tuple(ll[v] for v in external)
    ext_brackets=tuple((ext_map[a],ext_map[z],c) for a,z,c in remaining_bb)
    labels=sorted(hole_groups)
    off=len(ext_labels)
    result={}
    for group,source_terms in enumerate(terms):
        for coefficient,tl,tb,te,free in source_terms:
            choices=[permutations(free.get(label,()),len(hole_groups[label])) for label in labels]
            for assignments in product(*choices):
                sub=dict(ext_map)
                for label,assignment in zip(labels,assignments):
                    sub.update((h,off+v) for h,v in zip(hole_groups[label],assignment))
                eps=tuple((off+a,off+z) for a,z in te)+tuple((sub[a],sub[z]) for a,z in context_ee)
                brackets=ext_brackets+tuple((off+a,off+z,c) for a,z,c in tb)
                for out,co in b.normalize_graph(ext_labels+tl,brackets,eps).items():
                    b.add_term(result,out,b.pmul(coefficient,co))
        if group==0 and terms[1]:
            # The matched pattern has the parent's maximum bracket degree.
            # Determinants cannot increase degree. Lower source terms plus
            # the same context therefore cannot produce/cancel any monomial
            # of degree degree(mon). If the prepared top group does not
            # lead on mon, this particular contextual replacement cannot apply.
            assert len(pattern[1])+len(remaining_bb)==p.degree(mon)
            if max(result,key=b.mkey,default=None)!=mon:
                stats['nonleading_contexts_rejected_before_lower_terms']+=1
                stats['lower_source_terms_not_substituted']+=len(terms[1])
                # Empty matching result means a rejected occurrence, not a
                # claim that the complete contracted identity vanishes.
                return {}
    return result


class FastContextReducer(EfficientReducer):
    def original_candidates(self,mon,only_m=False):
        if not hasattr(self,'_original_blocks'):
            self._original_blocks=BoundedCache(20000)
        ll,bb,ee,owners,edge_of=bp.graph_details(mon)
        seen=set()
        for a,z in ee:
            i,j=edge_of[a],edge_of[z]
            if bb[i][2]==bb[j][2]:continue
            sig=('M',bp.local_signature(mon,(i,j)))
            if sig in seen:continue
            seen.add(sig)
            block,rest,edges=bp.selected_block(mon,(i,j))
            bl,br,be=b.graph(block)
            candidates=[edge for edge in be if {
                next(t for t,x in enumerate(br) if edge[0] in x[:2]),
                next(t for t,x in enumerate(br) if edge[1] in x[:2])}==set(edges)]
            for x,y in candidates:
                endpoints=[]
                for v in (x,y):
                    aa,zz,color=next(edge for edge in br if v in edge[:2])
                    endpoints.append((color,bl[zz if aa==v else aa]))
                endpoints.sort(reverse=True)
                endpoint_labels=tuple(i for color,i in endpoints)
                leading=bp.momentum_leading_label(*endpoint_labels,self.n)
                if self.unique_momentum_lm and bl[x]!=leading:
                    self.stats['nonleading_momentum_occurrences_skipped']+=1
                    continue
                key=('M',block,x,y)
                if key not in self._original_blocks:
                    row={}
                    for k in range(1,self.n+1):
                        labels=list(bl);labels[x]=labels[y]=k
                        for m,co in b.normalize_graph(tuple(labels),br,be).items():
                            b.add_term(row,m,co)
                    row,factor,scale=p.primitive(row)
                    self._original_blocks[key]=(row,factor)
                    self.stats['original_block_substitutions']+=1
                else:self.stats['original_block_reuses']+=1
                row,factor=self._original_blocks[key]
                if row:
                    pid=self.original_ids['M',endpoint_labels]
                    yield row,rest+factor,{'parent':pid,'kind':'M','block':block,
                        'placement':[x,y],'removed_product':factor,
                        'matched_momentum':bl[x],'prescribed_momentum':leading}
        if only_m:return
        for i,j in combinations(range(len(bb)),2):
            if bb[i][2]!=bb[j][2]:continue
            labels=sorted(ll[v] for k in (i,j) for v in bb[k][:2])
            if max(Counter(labels).values())>2:continue
            sig=('S',bp.local_signature(mon,(i,j)))
            if sig in seen:continue
            seen.add(sig)
            block,rest,edges=bp.selected_block(mon,(i,j))
            bl,br,be=b.graph(block)
            a,z,color=br[edges[0]];x,y,_=br[edges[1]]
            key=('S',block,edges)
            if key not in self._original_blocks:
                row=dict(b.normalize_graph(bl,br,be))
                for replacement,sign in [(((a,x,color),(z,y,color)),-1),
                                         (((a,y,color),(z,x,color)),1)]:
                    bs=list(br);bs[edges[0]],bs[edges[1]]=replacement
                    for m,co in b.normalize_graph(bl,tuple(bs),be).items():
                        b.add_term(row,m,{e:sign*v for e,v in co.items()})
                row,factor,scale=p.primitive(row)
                self._original_blocks[key]=(row,factor)
                self.stats['original_block_substitutions']+=1
            else:self.stats['original_block_reuses']+=1
            row,factor=self._original_blocks[key]
            if row:
                pid=self.original_ids['S',(color,*labels)]
                yield row,rest+factor,{'parent':pid,'kind':'S','block':block,
                    'placement':edges,'removed_product':factor}

    def embedded_derived_identity(self,parent,ti,pattern,block,edges,port_map):
        if not hasattr(self,'_prepared_parent_terms'):
            self._prepared_parent_terms={}
        key=(parent['id'],parent.get('revision',0),ti,block,edges,
             tuple(sorted(port_map.items())))
        if key not in self._block_embeddings:
            pid=parent['id']
            old=self._prepared_parent_terms.get(pid)
            if old is None or old[0] is not parent['row']:
                old=(parent['row'],prepared_terms(parent['row']))
                self._prepared_parent_terms[pid]=old
            contextual=embed_prepared(old[1],pattern,block,edges,port_map,self.stats)
            if getattr(self,'audit_prepared_embeddings',False):
                expected=bp.embed_physical(parent['row'],pattern,block,edges,port_map)
                if contextual:
                    assert contextual==expected,'Prepared substitution changed an identity'
                else:
                    assert not expected or max(expected,key=_original_mkey)!=block, 'Lost an actual LM'
                self.stats['exact_full_embedding_audits']+=1
            self._block_embeddings[key]=contextual
            self.stats['minimal_block_embedding_misses']+=1
        else:self.stats['minimal_block_embedding_hits']+=1
        return self._block_embeddings[key]

    def _actions(self,mon,first_only=False):
        key=(self.version,mon,first_only)
        if key in self.action_cache:
            self.stats['action_cache_hits']+=1
            return self.action_cache[key]
        self.stats['input_monomials_examined']+=1
        if first_only:
            momentum=self.momentum_actions(mon)
            if momentum:return momentum[:1]
        actions=[];seen={}

        def accept(row,rest,source,prepared_head=None):
            if not row:return
            # All contextual rows already underwent determinant preparation.
            # Untouched tensor-product factors preserve the structural order.
            # Primitive coefficient/factor removal and reinsertion do not
            # change the support of row*rest, so this rejects only non-LMs.
            head=prepared_head if prepared_head is not None else max(row,key=b.mkey)
            if b.mono(head+rest)!=mon:
                self.stats['nonleading_rows_rejected_before_primitive']+=1
                return
            if prepared_head is None:
                row,common,scale=p.primitive(row)
                primitive_head=p.quotient(head,common)
            else:
                common=();scale=b.ONE;primitive_head=head
            whole=p.multiply(row,b.mono(rest+common))
            encoding=p.encode(whole)
            if encoding in seen:
                previous=seen[encoding]
                ids=set(previous.get('equivalent_parent_ids',[previous['parent']]))
                ids.update(source.get('equivalent_parent_ids',[source['parent']]))
                previous['equivalent_parent_ids']=sorted(ids)
                return
            source=dict(source)
            seen[encoding]=source
            source['coefficient_scale_removed']=scale
            actions.append((whole,source))
            row_encoding=p.encode(row)
            if row_encoding not in self.cache_encodings[primitive_head]:
                self.cache[primitive_head].append((row,source))
                self.cache_encodings[primitive_head].add(row_encoding)
                self.stats['cached_contextual_replacements']+=1
            if first_only:raise bp.FirstAction(actions[-1])

        for k in range(1,len(mon)+1):
            for pos in combinations(range(len(mon)),k):
                head=tuple(mon[i] for i in pos)
                rest=p.quotient(mon,head)
                for row,source in list(self.cache.get(head,())):
                    accept(row,rest,source,prepared_head=head)
        if mon not in self.original_cache:
            original=[]
            for row,rest,source in self.original_candidates(mon):
                original.append((row,rest,source))
                if source['kind']=='S':
                    rkey=p.encode(row)
                    if rkey in self.momentum_polynomial_cache:
                        self.stats['momentum_polynomial_cache_hits']+=1
                    else:self.momentum_polynomial_cache[rkey]=self.reduce(row,only_m=True,trace=True)
                    reduced,den,steps=self.momentum_polynomial_cache[rkey]
                    if reduced and p.encode(reduced)!=p.encode(row):
                        if max(reduced,key=b.mkey)==max(row,key=b.mkey):
                            original.append((reduced,rest,{**source,'momentum_reduced':True,
                                            'momentum_steps':steps,'denominator':den}))
                        else:self.stats['changed_S_heads_not_cached_as_descendants']+=1
            self.original_cache[mon]=original
        for row,rest,source in self.original_cache[mon]:accept(row,rest,source)
        ml,mb,me=b.graph(mon)
        signature=Counter((c,tuple(sorted((ml[a],ml[z])))) for a,z,c in mb)
        for pid,ti,pattern,required in self.matching_derived_patterns(mon,signature):
            if len(pattern[1])>=p.degree(mon) or any(signature[k]<v for k,v in required.items()):continue
            parent=self.parents[pid];dkey=(pid,ti,mon)
            if dkey in self.derived_context_cache:
                for contextual,rest,source in self.derived_context_cache[dkey]:accept(contextual,rest,source)
                continue
            materialized=[]
            _,_,_,owners,_=bp.graph_details(mon)
            contexts_seen=set()
            for selected,mapping in bp.graph_matches(pattern,mon):
                block,rest,edges=bp.selected_block(mon,selected)
                touched={owners[e] for e in selected}
                old_edges=[i for i in range(len(mb)) if owners[i] in touched]
                renumber={v:i for i,v in enumerate(old_edges)}
                local_map={v:2*renumber[w//2]+w%2 for v,w in mapping.items()}
                csig=(block,edges,tuple(sorted(local_map.items())))
                if csig in contexts_seen:continue
                contexts_seen.add(csig)
                contextual=self.embedded_derived_identity(parent,ti,pattern,block,edges,local_map)
                self.stats['derived_contexts_materialized']+=1
                source={'parent':pid,'kind':'derived-context','block':block,'pattern_term':ti,
                        'selected_edges':edges,'port_map':local_map}
                materialized.append((contextual,rest,source))
                accept(contextual,rest,source)
            self.derived_context_cache[dkey]=materialized
        self.action_cache[key]=actions
        return actions


class FastContextB2(EfficientB2):
    def setup_efficient_caches(self,resuming):
        super().setup_efficient_caches(resuming)
        self.engine.__class__=FastContextReducer
        install_primitives()
        self.report_options['contextual_matching']='prepared_graphs_early_actual_LM_exact_structural_order'


if __name__=='__main__':
    import compact_b2_restart as compact
    compact.CompactB2=FastContextB2
    compact.main()
