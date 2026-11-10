"""Exact bounded tensor relation construction, all representations, no Mathematica.

Graphs carry oriented Lorentz brackets and little-group epsilon edges.
Mass-polynomial coefficients are exact. Gaussian S-cancellation uses the
actual prepared graph head, with fraction-free arithmetic over Q(m_1,...,m_4).
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product, combinations, combinations_with_replacement
from fractions import Fraction
from math import gcd
from pathlib import Path
import argparse
import json
import time
import check_contraction_sensitive_order as order

ZERO = (0,0,0,0)
ONE = {ZERO: 1}
TIMES = defaultdict(float)
COUNTS = Counter()
UNITS = {}
CERTS = []
ORDER_BOUND = 4


def padd(a, b, scale=1):
    out = dict(a)
    for k,v in b.items():
        out[k] = out.get(k,0) + scale*v
        if not out[k]:
            del out[k]
    return out


def pmul(a,b):
    out = {}
    for ea,va in a.items():
        for eb,vb in b.items():
            e = tuple(x+y for x,y in zip(ea,eb))
            out[e] = out.get(e,0) + va*vb
    return {k:v for k,v in out.items() if v}


def mass(i, power=1, sign=1):
    e = [0]*4
    e[i-1] = power
    return {tuple(e): sign}


def add_term(row, mon, coeff):
    v = padd(row.get(mon,{}), coeff)
    if v:
        row[mon] = v
    else:
        row.pop(mon,None)


def mono(units):
    return tuple(sorted(units))


def canonical_chain(labels,colors):
    labels,colors=tuple(labels),tuple(colors)
    rev=(labels[::-1], colors[::-1])
    if (labels,colors)==rev:
        return 0, None
    if rev < (labels,colors):
        return -1, order.chain(labels,colors)
    return 1, order.chain(labels,colors)


@lru_cache(None)
def normalize_unit(kind,labels,colors):
    """Return a polynomial in retained units; coefficients contain masses."""
    n=len(colors)
    # Same-particle bracket B_ii=m_i E: E^2=-I.
    for j in range(n):
        k=(j+1)%len(labels)
        if labels[j]==labels[k]:
            if kind==0 and n==1:
                return {}  # epsilon in symmetrized free indices
            if kind==1 and n==1:
                return {():mass(labels[j],sign=2)}
            ll=list(labels); cc=list(colors)
            # Drop one of the equal vertices and the bracket between them.
            del cc[j]
            del ll[j]
            out=normalize_unit(kind,tuple(ll),tuple(cc))
            return {m:pmul(mass(labels[j],sign=-1),c) for m,c in out.items()}
    # Same-chirality internal pairing: B_ik E B_kj=-m_k B_ij.
    nodes=range(n) if kind else range(1,n)
    for j in nodes:
        prev=(j-1)%n
        if colors[prev]==colors[j]:
            ll=list(labels); cc=list(colors)
            del ll[j]; del cc[j]
            out=normalize_unit(kind,tuple(ll),tuple(cc))
            return {m:pmul(mass(labels[j],sign=-1),c) for m,c in out.items()}
    if kind==0:
        sign,u=canonical_chain(labels,colors)
        return {mono([u]):{ZERO:sign}} if sign else {}
    # Four-trace repeated opposite label, in tau=-Tr(B E ... B E)
    # convention: tau(i,j,i,k)=-tau(i,j)tau(i,k)-m_i^2 tau(j,k).
    if n==4 and len(set(labels))<4:
        j=next(j for j in range(2) if labels[j]==labels[j+2])
        i,a,b=labels[j],labels[(j+1)%4],labels[(j+3)%4]
        def tau(x,y):
            return order.trace([x,y],[1,0])
        out={mono([tau(i,a),tau(i,b)]):{ZERO:-1}}
        if a==b:
            add_term(out,(),pmul(mass(i,2),mass(a,2,2)))
        else:
            add_term(out,mono([tau(a,b)]),mass(i,2,-1))
        return out
    if n==6 and len(set(labels))<=3:
        # The parity-odd trace vanishes with at most three distinct momenta.
        # tau_6 = (1/4) sum_pairings sign(pairing) tau_2 tau_2 tau_2,
        # including tau(i,i)=-2 m_i^2. This follows by Clifford
        # anticommutation; it is preparation, not a fitted identity.
        def pairings(seq):
            if not seq:
                yield 1, ()
                return
            for k in range(1,len(seq)):
                for sign,pairs in pairings(seq[1:k]+seq[k+1:]):
                    yield (-1)**(k+1)*sign, ((seq[0],seq[k]),)+pairs
        out={}
        for sign,pairs in pairings(tuple(labels)):
            mon=[]; co={ZERO:sign}
            for a,z in pairs:
                if a==z: co=pmul(co,mass(a,2,-2))
                else: mon.append(order.trace((a,z),(1,0)))
            add_term(out,mono(mon),co)
        assert all(v%4==0 for co in out.values() for v in co.values())
        return {m:{e:v//4 for e,v in co.items()} for m,co in out.items()}
    assert n in (2,4) and (n==2 or len(set(labels))==4)
    u=order.trace(labels,colors)
    return {mono([u]):ONE}


def graph(mon):
    labels=[]; brackets=[]; eps=[]
    for length,kind,ll,cc in mon:
        first=len(labels)
        for j,c in enumerate(cc):
            a=len(labels)
            labels.extend([ll[j],ll[(j+1)%len(ll)]])
            brackets.append((a,a+1,c))
            if j:
                eps.append((a-1,a))
        if kind:
            # The stored trace is minus the ordinary matrix trace.
            eps.append((first, len(labels)-1))
    return tuple(labels),tuple(brackets),tuple(eps)


def normalize_graph(labels,brackets,eps):
    badj={}; eadj={}
    for a,b,c in brackets:
        badj[a]=(b,c,1); badj[b]=(a,c,-1)
    for a,b in eps:
        eadj[a]=(b,1); eadj[b]=(a,-1)
    remaining=set(badj)
    result={():ONE}
    while remaining:
        endpoints=remaining-set(eadj)
        start=min(endpoints) if endpoints else min(remaining)
        kind=int(not endpoints)
        ll=[labels[start]]; cc=[]; sign=1; v=start
        while True:
            w,c,s=badj[v]
            sign*=s
            remaining.remove(v); remaining.remove(w)
            cc.append(c)
            if w not in eadj:
                ll.append(labels[w]); break
            v,s=eadj[w]; sign*=s
            if v==start:
                sign*=-1  # closed product = - stored tau
                break
            ll.append(labels[w])
        unit=normalize_unit(kind,tuple(ll),tuple(cc))
        combined={}
        for m,a in result.items():
            for u,b in unit.items():
                add_term(combined,mono(m+u),pmul(a,{e:sign*v for e,v in b.items()}))
        result=combined
        if not result:
            break
    return result


def alphabet(bound):
    units=set()
    for d in range(1,bound+1):
        for ll in product(range(1,5),repeat=d+1):
            if any(a==b for a,b in zip(ll,ll[1:])):
                continue
            for c in (0,1):
                cc=tuple((c+j)%2 for j in range(d))
                _,u=canonical_chain(ll,cc)
                if u:
                    units.add(u)
    if bound>=2:
        for pair in combinations(range(1,5),2):
            units.add(order.trace(pair,[1,0]))
    if bound>=4:
        for ll in product(range(1,5),repeat=4):
            if len(set(ll))==4:
                units.add(order.trace(ll,[1,0,1,0]))
    return sorted(units)


def monomials(units,bound):
    result=[()]
    def visit(prefix,start,remaining):
        for i in range(start,len(units)):
            u=units[i]
            if u[0]>remaining:
                break
            m=prefix+(u,)
            result.append(m)
            visit(m,i,remaining-u[0])
    visit((),0,bound)
    return result


@lru_cache(None)
def sector(mon):
    counts=[0]*4
    for _,kind,ll,_ in mon:
        if not kind:
            counts[ll[0]-1]+=1; counts[ll[-1]-1]+=1
    return tuple(counts)


@lru_cache(None)
def mkey(mon):
    # Fixed structural blocks; ascending factor lists are equivalent to
    # signed multiplicity lex once the length histogram is tied.
    h=tuple(sum(u[0]==d for u in mon) for d in range(ORDER_BOUND,0,-1))
    t=tuple(-sum(u[0]==d and u[1] for u in mon) for d in range(ORDER_BOUND,0,-1))
    fillings=tuple(tuple(sorted(order.unit_key(u) for u in mon if u[0]==d))
                   for d in range(ORDER_BOUND,0,-1))
    return sum(u[0] for u in mon),h,t,fillings


def primitive(row):
    """Remove common integer content and mass monomial, over generic masses."""
    if not row:
        return row,ONE
    entries=[(e,v) for c in row.values() for e,v in c.items()]
    g=0
    for _,v in entries:
        g=gcd(g,v)
    common=tuple(min(e[i] for e,_ in entries) for i in range(4))
    pivot=row[max(row,key=mkey)]
    if pivot[max(pivot)]<0:
        g=-g
    if g==1 and common==ZERO:
        return row,ONE
    out={m:{tuple(a-b for a,b in zip(e,common)):v//g for e,v in c.items()}
         for m,c in row.items()}
    return out,{common:g}


def row_encoding(row):
    return tuple(sorted((m,tuple(sorted(c.items()))) for m,c in row.items()))


def seeds(mon):
    """All local elementary Schouten and momentum insertions on a monomial."""
    labels,brackets,eps=graph(mon)
    for i,j in combinations(range(len(brackets)),2):
        a,b,c=brackets[i]; x,y,other=brackets[j]
        if c!=other:
            continue
        row=dict(normalize_graph(labels,brackets,eps))
        for new,sign in [(((a,x,c),(b,y,c)),-1),
                         (((a,y,c),(b,x,c)),1)]:
            bb=list(brackets); bb[i],bb[j]=new
            for m,co in normalize_graph(labels,tuple(bb),eps).items():
                add_term(row,m,{e:sign*v for e,v in co.items()})
        yield "Schouten",(i,j),row
    # Sum of momenta at each little-group contraction node.
    for i,(a,b) in enumerate(eps):
        color={v:c for x,y,c in brackets for v in (x,y)}
        assert color[a]!=color[b]
        row={}
        for k in range(1,5):
            ll=list(labels); ll[a]=ll[b]=k
            for m,co in normalize_graph(tuple(ll),brackets,eps).items():
                add_term(row,m,co)
        yield "momentum",(i,),row


def contexts(row,head,factor,momentum_head_only=True):
    """Physical symmetric contexts; sum all free-slot assignments.

    A contracted factor endpoint must meet only opposite-chirality head
    endpoints. Lower terms are determinant-prepared after attachment.
    """
    hl,hb,he=graph(head)
    occupied={v for e in he for v in e}
    hc={v:c for a,b,c in hb for v in (a,b)}
    allowed=[]
    for mask in range(4):
        valid=True
        for j in range(2):
            if mask & (1<<j):
                old=[v for v,i in enumerate(hl) if i==factor[2][j] and v not in occupied]
                if not old or (momentum_head_only and any(hc[v]==factor[3][0] for v in old)):
                    valid=False
        if valid:
            allowed.append(mask)
    for mask in allowed:
        out={}
        for mon,co in row.items():
            ll,bb,ee=graph(mon)
            used={v for e in ee for v in e}
            offset=len(ll)
            choices=[]
            for j in range(2):
                choices.append([v for v,i in enumerate(ll)
                                if i==factor[2][j] and v not in used]
                               if mask&(1<<j) else [None])
            for selected in product(*choices):
                eps=ee+tuple((v,offset+j) for j,v in enumerate(selected) if v is not None)
                raw=normalize_graph(ll+factor[2],bb+((offset,offset+1,factor[3][0]),),eps)
                for m,c in raw.items():
                    add_term(out,m,pmul(co,c))
        yield mask,out


class Elimination:
    def __init__(self,deduplicate=True):
        self.deduplicate=deduplicate
        self.basis={}
        self.seen=set()
        self.rows=[]
        self.events=[]
        self.max_terms=0
        self.max_coeff_terms=0
        self.context_queue=[]

    def insert(self,row,source):
        row,divisor=primitive(row)
        if not row:
            COUNTS["zero_seed"]+=1
            return
        if self.deduplicate:
            enc=row_encoding(row)
            if enc in self.seen:
                COUNTS["duplicate_seed"]+=1
                return
            self.seen.add(enc)
        node=len(self.rows)
        self.rows.append(row)
        self.events.append(("seed",source,divisor))
        COUNTS["unique_seed"]+=1
        start=time.perf_counter()
        while row:
            head=max(row,key=mkey)
            if head not in self.basis:
                self.basis[head]=node
                self.context_queue.append((head,node))
                COUNTS["new_pivot"]+=1
                break
            bid=self.basis[head]
            other=self.rows[bid]
            a,b=row[head],other[head]
            result={}
            # Fraction-free S-cancellation: b*row - a*other.
            for m,c in row.items():
                add_term(result,m,pmul(b,c))
            for m,c in other.items():
                add_term(result,m,{e:-v for e,v in pmul(a,c).items()})
            assert head not in result
            result,divisor=primitive(result)
            nid=len(self.rows)
            self.rows.append(result)
            self.events.append(("cancel",node,bid,a,b,divisor))
            node=nid; row=result
            COUNTS["S_cancellations"]+=1
            self.max_terms=max(self.max_terms,len(row))
            self.max_coeff_terms=max(self.max_coeff_terms,
                                     max(map(len,row.values()),default=0))
        if not row:
            COUNTS["zero_remainder"]+=1
        TIMES["reduction"]+=time.perf_counter()-start


def serial_poly(p):
    return [[list(e),v] for e,v in sorted(p.items())]


def serial_row(row,ids):
    return [[ids[m],serial_poly(c)] for m,c in sorted(row.items(),key=lambda x:mkey(x[0]),reverse=True)]


def main():
    global mkey
    parser=argparse.ArgumentParser()
    parser.add_argument("--degree",type=int,default=4,choices=range(1,5))
    parser.add_argument("--no-dedup",action="store_true")
    parser.add_argument("--uncached-order",action="store_true")
    parser.add_argument("--tag",default="")
    args=parser.parse_args()
    if args.uncached_order:
        mkey=mkey.__wrapped__
    start=time.perf_counter()
    units=alphabet(args.degree)
    mons=monomials(units,args.degree)
    mons.sort(key=lambda m:(sum(u[0] for u in m),sector(m),mkey(m)))
    ids={m:i for i,m in enumerate(mons)}
    TIMES["alphabet"]=time.perf_counter()-start
    engine=Elimination(not args.no_dedup)
    for idx,mon in enumerate(mons):
        tick=time.perf_counter()
        relations=list(seeds(mon))
        TIMES["seed_preparation"]+=time.perf_counter()-tick
        for kind,placement,row in relations:
            COUNTS["raw_"+kind]+=1
            assert all(m in ids and sector(m)==sector(mon) for m in row)
            engine.insert(row,(ids[mon],kind,placement))
        if idx%1000==0:
            print(f"monomials {idx}/{len(mons)}, rules {len(engine.basis)}, elapsed {time.perf_counter()-start:.2f}s",flush=True)
    elementary_rules=len(engine.basis)
    # Closing under admissible one-bracket physical contexts also tests
    # newly discovered low-degree remainders, not just initial seeds.
    position=0
    factors=[u for u in units if u[0]==1]
    while position<len(engine.context_queue):
        head,node=engine.context_queue[position]
        position+=1
        if sum(u[0] for u in head)>=args.degree:
            continue
        for factor in factors:
            tick=time.perf_counter()
            # Audit the full physical tensor map, including mixed-chirality
            # symmetrization branches. These are prepared construction
            # identities, never forbidden raw runtime contraction rules.
            attached=list(contexts(engine.rows[node],head,factor,False))
            TIMES["descendant_preparation"]+=time.perf_counter()-tick
            for mask,row in attached:
                COUNTS["descendant_contexts"]+=1
                assert all(m in ids for m in row)
                assert len(set(sector(m) for m in row))<=1
                engine.insert(row,("context",node,ids[mono([factor])],mask))
    COUNTS["new_pivots_from_descendants"]=len(engine.basis)-elementary_rules
    catalog=[]
    for head,node in sorted(engine.basis.items(),key=lambda kv:mkey(kv[0]),reverse=True):
        catalog.append({"head":ids[head],"certificate":node,
                        "row":serial_row(engine.rows[node],ids)})
    events=[]
    for ev in engine.events:
        if ev[0]=="seed":
            events.append(["seed",ev[1],serial_poly(ev[2])])
        else:
            events.append(["cancel",ev[1],ev[2],*[serial_poly(p) for p in ev[3:]]])
    bysector=Counter(sector(h) for h in engine.basis)
    report={
        "n":4,"bracket_degree_bound":args.degree,
        "all_external_representations":True,
        "scope":"All elementary momentum/Schouten insertions on retained graphs, followed by closure under determinant-prepared one-bracket physical tensor contexts, summing all free-slot assignments.",
        "not_claimed":"Unrestricted completion, higher-degree consequences, or unsymmetrized open-slot tensor normal forms.",
        "coefficient_field":"Q(m1,m2,m3,m4), generic masses; stored rows polynomial",
        "unit_count":len(units),"monomial_count":len(mons),
        "representation_sector_count":len(set(map(sector,mons))),
        "rule_count":len(catalog),"sectors_with_rules":len(bysector),
        "rules_by_head_degree":dict(Counter(sum(u[0] for u in h) for h in engine.basis)),
        "counts":dict(COUNTS),"timings_seconds":dict(TIMES),
        "total_seconds":time.perf_counter()-start,
        "max_intermediate_terms":engine.max_terms,
        "max_mass_coefficient_terms":engine.max_coeff_terms,
        "certificate_nodes":len(events),"mathematica_started":False,
        "deduplication":not args.no_dedup,
        "cached_order_keys":not args.uncached_order,
    }
    out=Path(__file__).parent/(f"bounded_n4_d{args.degree}"+("_"+args.tag if args.tag else ""))
    out.mkdir(exist_ok=True)
    (out/"report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    payload={"report":report,"monomials":mons,"rules":catalog,"certificates":events}
    (out/"catalog.json").write_text(json.dumps(payload,separators=(",",":"))+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2),flush=True)


if __name__=="__main__":
    main()
