"""Rule-driven finite-window construction; no amplitude/basis enumeration.

Original identities retain named free slots until attachments are made.
Derived physical identities use symmetric contractions, not arbitrary slots.
The older exhaustive builder supplies graph preparation and exact arithmetic
only. Its alphabet(), monomials(), seeds(), and main() are never called.
"""
from collections import Counter, defaultdict, deque
from itertools import combinations, combinations_with_replacement, product
from functools import lru_cache
from pathlib import Path
from math import gcd
import json
import time
import argparse
import build_bounded_four_point as b

ROOT = Path(__file__).parent / "parent_descendants_n4_d4"
PARTICLES = 4

def degree(m):
    return sum(u[0] for u in m)

def primitive(row):
    row, scale = b.primitive(row)
    if not row:
        return row, (), scale
    common = Counter(next(iter(row)))
    for m in row:
        common &= Counter(m)
    factor = tuple(sorted(common.elements()))
    if factor:
        reduced = {}
        for m, c in row.items():
            rest = list(m)
            for u in factor:
                rest.remove(u)
            b.add_term(reduced, tuple(rest), c)
        row = reduced
    return row, factor, scale

def encode(row):
    return b.row_encoding(row)

def multiply(row, factor):
    return {b.mono(m+factor): c for m,c in row.items()}

def subtract(a, ah, r, rh):
    out = {}
    for m,c in a.items():
        b.add_term(out,m,b.pmul(rh,c))
    for m,c in r.items():
        b.add_term(out,m,{e:-v for e,v in b.pmul(ah,c).items()})
    return out

def quotient(m,h):
    rest=list(m)
    for u in h:
        if u not in rest:
            return None
        rest.remove(u)
    return tuple(rest)

def lcm(a,c):
    return tuple(sorted((Counter(a)|Counter(c)).elements()))

def raw_originals():
    for i,j in product(range(1,PARTICLES+1), repeat=2):
        terms=[(1,(i,k,k,j),((0,1,1),(2,3,0)),((1,2),)) for k in range(1,PARTICLES+1)]
        yield "M", [i,j], terms
    for chirality in (1,0):
        for labels in combinations_with_replacement(range(1,PARTICLES+1),4):
            terms=[(s,labels,tuple((a,c,chirality) for a,c in pairs),())
                   for s,pairs in [(1,((0,1),(2,3))),(-1,((0,2),(1,3))),
                                   (1,((0,3),(1,2)))]]
            yield "S", [chirality,*labels], terms

def project(raw):
    out={}
    for sign,ll,bb,ee in raw:
        for m,c in b.normalize_graph(ll,bb,ee).items():
            b.add_term(out,m,{e:sign*v for e,v in c.items()})
    return out

def raw_children(raw, added, bound):
    _,ll,bb,ee=raw[0]
    used={v for e in ee for v in e}
    color={v:c for a,d,c in bb for v in (a,d)}
    free=[v for v in range(len(ll)) if v not in used]
    # A closure consumes free ports but adds no spectator.
    for a,d in combinations(free,2):
        if ll[a]==ll[d] and color[a]!=color[d]:
            yield ["close",a,d],[(s,l,br,ep+((a,d),)) for s,l,br,ep in raw],added
    if len(bb)>=bound:
        return
    for i,j in combinations(range(1,PARTICLES+1),2):
        for c in (0,1):
            choices=[[None]+[v for v in free if ll[v]==k and color[v]!=c] for k in (i,j)]
            for a,d in product(*choices):
                if a is None and d is None:
                    continue # pure tensor-product multiples are not new rules
                off=len(ll)
                eps=tuple((v,off+t) for t,v in enumerate((a,d)) if v is not None)
                desc=[(s,l+(i,j),br+((off,off+1,c),),ep+eps) for s,l,br,ep in raw]
                yield ["attach",i,j,c,a,d],desc,added+1

def raw_contexts(raw,bound):
    todo=[(raw,[],0)]
    seen=set()
    while todo:
        r,path,added=todo.pop()
        key=tuple((s,ll,bb,tuple(sorted(ee))) for s,ll,bb,ee in r)
        if key in seen:
            continue
        seen.add(key)
        yield path,r,project(r)
        for op,child,k in raw_children(r,added,bound):
            todo.append((child,path+[op],k))

def close_physical(row,label):
    out={}
    for m,co in row.items():
        ll,bb,ee=b.graph(m)
        used={v for e in ee for v in e}
        free=[v for v,i in enumerate(ll) if i==label and v not in used]
        for a,d in combinations(free,2):
            for n,c in b.normalize_graph(ll,bb,ee+((a,d),)).items():
                b.add_term(out,n,b.pmul(co,c))
    return out

def physical_contexts(row,bound,deduplicate=True):
    # Parent-level potential LMs: top-degree terms. Exact contextual head
    # decisions are made after collecting; lower-degree fallback is retained.
    initial_degree=max(map(degree,row))
    todo=[(row,[])]
    seen=set()
    while todo:
        r,path=todo.pop()
        # Keep tensor factors until every attachment is completed. Removing
        # one now would erase its possible later contractions.
        r,scale=b.primitive(r)
        if not r or (deduplicate and encode(r) in seen):
            continue
        seen.add(encode(r))
        yield path,r
        d=max(map(degree,r))
        tops=[m for m in r if degree(m)==d]
        # A symmetric same-particle pair is annihilated by epsilon. Therefore
        # closures of already symmetric parents are zero; do not pick a slot.
        if initial_degree+len(path)>=bound:
            continue
        allowed=set()
        for h in tops:
            for i,j in combinations(range(1,PARTICLES+1),2):
                for c in (0,1):
                    f=b.order.chain((i,j),(c,))
                    for mask,_ in b.contexts({h:b.ONE},h,f,True):
                        if mask:
                            allowed.add((f,mask))
        for f,mask in sorted(allowed):
            # Apply the full physical tensor, including lower mass terms.
            h=next(m for m in tops if mask in dict(b.contexts({m:b.ONE},m,f,True)))
            child=dict(b.contexts(r,h,f,False))[mask]
            todo.append((child,path+[["attach-symmetric",f,mask]]))

class Constructor:
    def __init__(self,bound=4):
        self.bound=bound
        self.parents=[]
        self.parent_by_encoding={}
        self.instances=[]
        self.instance_by_encoding={}
        self.head_index={}
        self.by_unit=defaultdict(set)
        self.pending=deque()
        self.pairs=deque()
        self.pair_seen=set()
        self.stats=Counter()
        self.events=[]

    def add_instance(self,row,parent,path):
        row,common,scale=primitive(row)
        if not row:
            self.stats["zero_contexts"]+=1
            return
        if max(map(degree,row))>self.bound:
            self.stats["over_bound"]+=1
            return
        key=encode(row)
        source={"parent":parent,"context":path,"removed_product":common,"scale":scale}
        if key in self.instance_by_encoding:
            self.instances[self.instance_by_encoding[key]]["sources"].append(source)
            self.stats["duplicate_contexts"]+=1
            return
        i=len(self.instances)
        self.instance_by_encoding[key]=i
        self.instances.append({"row":row,"sources":[source]})
        self.pending.append(i)

    def add_parent(self,row,origin,raw=None):
        if raw is None:
            row,common,scale=primitive(row)
            key=encode(row)
            if not row or key in self.parent_by_encoding:
                return None
            self.parent_by_encoding[key]=len(self.parents)
        p=len(self.parents)
        record={"row":row,"origin":origin,"raw":raw}
        self.parents.append(record)
        contexts=( (path,r) for path,rr,r in raw_contexts(raw,self.bound)) if raw is not None else physical_contexts(row,self.bound)
        for path,r in contexts:
            self.stats["contexts_prepared"]+=1
            self.add_instance(r,p,path)
        return p

    def index(self,i):
        row=self.instances[i]["row"]
        h=max(row,key=b.mkey)
        # The scheduling index is transient construction data, not B rules.
        if h in self.head_index:
            self.queue_pair(i,self.head_index[h])
        else:
            self.head_index[h]=i
        candidates=set()
        for u in h:
            candidates |= self.by_unit[u]
        for j in sorted(candidates):
            self.queue_pair(i,j)
        for u in h:
            self.by_unit[u].add(i)

    def queue_pair(self,i,j):
        if i==j:
            return
        a,c=sorted((i,j))
        if (a,c) in self.pair_seen:
            return
        h=max(self.instances[a]["row"],key=b.mkey)
        k=max(self.instances[c]["row"],key=b.mkey)
        host=lcm(h,k)
        if degree(host)>self.bound:
            return
        self.pair_seen.add((a,c))
        self.pairs.append((a,c,host))

    def divisor(self,m):
        # Only whole connected units are canceled here; contraction contexts
        # have already been prepared as explicit instances with parent links.
        for k in range(1,len(m)+1):
            for pos in combinations(range(len(m)),k):
                h=tuple(m[t] for t in pos)
                if h in self.head_index:
                    return self.head_index[h],quotient(m,h)
        return None

    def reduce(self,row):
        out={}
        steps=[]
        while row:
            h=max(row,key=b.mkey)
            found=self.divisor(h)
            if found is None:
                out[h]=row.pop(h)
                continue
            i,factor=found
            r=multiply(self.instances[i]["row"],factor)
            rh=r[h]; ah=row[h]
            # Retain exact fractional-free coefficients also on already
            # irreducible terms; normalization is done once at the end.
            row=subtract(row,ah,r,rh)
            out={m:b.pmul(c,rh) for m,c in out.items()}
            steps.append([i,factor,ah,rh])
            self.stats["reduction_steps"]+=1
        out,common,scale=primitive(out)
        return out,steps,common,scale

    def run(self):
        started=time.perf_counter()
        for family,labels,raw in raw_originals():
            self.add_parent(project(raw),{"family":family,"labels":labels},raw)
        self.stats["original_parent_records"]=len(self.parents)
        initial=time.perf_counter()-started
        while self.pending or self.pairs:
            while self.pending:
                self.index(self.pending.popleft())
            if not self.pairs:
                break
            i,j,host=self.pairs.popleft()
            a=multiply(self.instances[i]["row"],quotient(host,max(self.instances[i]["row"],key=b.mkey)))
            c=multiply(self.instances[j]["row"],quotient(host,max(self.instances[j]["row"],key=b.mkey)))
            row=subtract(a,a[host],c,c[host])
            r,steps,common,scale=self.reduce(row)
            self.stats["S_pairs"]+=1
            if r:
                origin={"family":"S-polynomial","left":i,"right":j,"host":host,
                        "left_coefficient":a[host],"right_coefficient":c[host],
                        "reduction_steps":steps,"removed_product":common,"scale":scale}
                p=self.add_parent(r,origin)
                self.stats["nonzero_S_remainders"]+=1
                if p is not None:
                    print(json.dumps({"new_parent":p,"degree":max(map(degree,r)),
                                      "terms":len(r),"queue":len(self.pairs)}),flush=True)
            else:
                self.stats["zero_S_remainders"]+=1
            if self.stats["S_pairs"]%10000==0:
                print(json.dumps({"checked":self.stats["S_pairs"],"pending":len(self.pairs),"parents":len(self.parents)}),flush=True)
        self.timings={"original_context_preparation":initial,"construction":time.perf_counter()-started}
        return self

def row_json(r):
    return [[m,[[e,c] for e,c in sorted(p.items())]] for m,p in sorted(r.items(),key=lambda x:b.mkey(x[0]),reverse=True)]

def safe(obj):
    if isinstance(obj,dict):
        if obj and all(isinstance(k,tuple) for k in obj):
            return [[safe(k),safe(v)] for k,v in obj.items()]
        return {k:safe(v) for k,v in obj.items()}
    if isinstance(obj,(tuple,list)):
        return [safe(v) for v in obj]
    return obj

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--degree",type=int,default=4,choices=(2,3,4))
    args=parser.parse_args()
    c=Constructor(args.degree).run()
    ROOT.mkdir(exist_ok=True)
    data={"parents":[{**{k:v for k,v in p.items() if k!="row"},"row":row_json(p["row"])} for p in c.parents],
          "instances":[{"row":row_json(p["row"]),"sources":p["sources"]} for p in c.instances],
          "stats":dict(c.stats),"timings":c.timings,"bound":args.degree}
    (ROOT/f"construction_d{args.degree}.json").write_text(json.dumps(safe(data),separators=(",",":")),encoding="utf-8")
    print(json.dumps({"parents":len(c.parents),"instances":len(c.instances),"stats":dict(c.stats),"timings":c.timings},indent=2),flush=True)

if __name__=="__main__":
    main()
