"""Replay exact certificates and evaluate the catalog on rational kinematics."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
import time
import build_bounded_four_point as b
import check_four_point_contextual_spairs as v


def freeze(x):
    return tuple(map(freeze,x)) if isinstance(x,list) else x


def poly(x):
    return {tuple(e):c for e,c in x}


def decode_row(x,mons):
    return {mons[i]:poly(c) for i,c in x}


def sample(rng):
    while True:
        masses={i:F(rng.randint(1,5)) for i in range(1,4)}
        left={i:v.random_frame(rng,masses[i]) for i in masses}
        right={i:v.random_frame(rng,masses[i]) for i in masses}
        p4=v.scale(-1,v.add(*(v.mul(left[i],v.E,v.trans(right[i])) for i in masses)))
        d=v.det(p4)
        if d<=0 or d.denominator!=1 or isqrt(d.numerator)**2!=d.numerator:
            continue
        masses[4]=F(isqrt(d.numerator))
        left[4]=((F(1),F(0)),(F(0),masses[4]))
        right[4]=v.trans(v.mul(v.inverse(v.mul(left[4],v.E)),p4))
        return v.Spinors(masses,left,right)


def evaluator(s,z):
    @lru_cache(None)
    def unit(u):
        d,kind,ll,cc=u
        pieces=[]
        for j,c in enumerate(cc):
            pieces.append((s.a if c else s.b)[ll[j],ll[(j+1)%len(ll)]])
            if kind or j<d-1:
                pieces.append(v.E)
        mat=v.mul(*pieces)
        if kind:
            return -mat[0][0]-mat[1][1]
        return sum(z[ll[0]][i]*mat[i][j]*z[ll[-1]][j]
                   for i,j in product(range(2),repeat=2))
    @lru_cache(None)
    def mon(m):
        out=F(1)
        for u in m:
            out*=unit(u)
        return out
    @lru_cache(None)
    def masspow(e):
        out=F(1)
        for i,k in enumerate(e,1):
            out*=s.m[i]**k
        return out
    def row(r):
        return sum(mon(m)*sum(c*masspow(e) for e,c in co.items())
                   for m,co in r.items())
    return row


def main():
    start=time.perf_counter()
    out=Path(__file__).parent/"bounded_n4_d4"
    data=json.loads((out/"catalog.json").read_text(encoding="utf-8"))
    mons=[freeze(m) for m in data["monomials"]]
    order_rng=random.Random(20261021)
    for _ in range(1000):
        x,y=order_rng.choices(mons,k=2)
        assert ((b.mkey(x)>b.mkey(y))-(b.mkey(x)<b.mkey(y)))==b.order.cmp(x,y)
    rows=[]; seed_cache={}
    def seed(source):
        if source[0]=="context":
            _,node,fi,mask=source
            parent=rows[node]
            head=max(parent,key=b.mkey)
            return dict(b.contexts(parent,head,mons[fi][0],False))[mask]
        mid,kind,placement=source
        if mid not in seed_cache:
            seed_cache[mid]={(k,p):r for k,p,r in b.seeds(mons[mid])}
        return seed_cache[mid][kind,tuple(placement)]
    for idx,event in enumerate(data["certificates"]):
        if event[0]=="seed":
            row,divisor=b.primitive(seed(event[1]))
            assert divisor==poly(event[2])
        else:
            _,a,c,pa,pc,div=event
            aa,bb=poly(pa),poly(pc)
            row={}
            for m,co in rows[a].items():
                b.add_term(row,m,b.pmul(bb,co))
            for m,co in rows[c].items():
                b.add_term(row,m,{e:-x for e,x in b.pmul(aa,co).items()})
            row,divisor=b.primitive(row)
            assert divisor==poly(div)
        rows.append(row)
    for rule in data["rules"]:
        row=decode_row(rule["row"],mons)
        assert rows[rule["certificate"]]==row
        head=mons[rule["head"]]
        assert max(row,key=b.mkey)==head
        assert len(set(map(b.sector,row)))==1
    from export_bounded_four_point import polynomial_tex
    worked=["# Recorded S-cancellations from the bounded run\n",
            "Each pair below has the same actual prepared head. The rows are exact momentum/Schouten consequences, with full ancestry in catalog.json.",
            "The displayed S-polynomial is coefficient-weighted subtraction, followed only by removal of common integer/mass content. Further ancestry may itself contain S-cancellations.\n"]
    for degree in (2,3,4):
        candidates=[]
        for rule in data["rules"]:
            node=rule["certificate"]
            ev=data["certificates"][node]
            if ev[0]=="cancel" and sum(u[0] for u in mons[rule["head"]])==degree:
                candidates.append((len(rows[ev[1]])+len(rows[ev[2]])+len(rows[node]),node))
        if not candidates:
            continue
        _,node=min(candidates)
        ev=data["certificates"][node]
        left,right=rows[ev[1]],rows[ev[2]]
        head=max(left,key=b.mkey)
        assert head==max(right,key=b.mkey)
        worked.extend([
            f"## Degree {degree}; certificate node {node}\n",
            "$$\nP="+polynomial_tex(left)+"=0\n$$\n",
            "$$\nQ="+polynomial_tex(right)+"=0\n$$\n",
            "$$\nH="+polynomial_tex({head:b.ONE})+"\n$$\n",
            "$$\nS=\\left("+polynomial_tex({():poly(ev[4])})+
            "\\right)P-\\left("+polynomial_tex({():poly(ev[3])})+"\\right)Q\n$$\n",
            "$$\nS=\\left("+polynomial_tex({():poly(ev[5])})+
            "\\right)\\left("+polynomial_tex(rows[node])+"\\right)=0.\n$$\n",
            "The common head cancels exactly. The largest remaining monomial is the new pivot; all displayed terms have the same external representation.\n",
        ])
    (out/"worked_spairs.md").write_text("\n\n".join(worked)+"\n",encoding="utf-8")
    replay_seconds=time.perf_counter()-start
    print(f"Replayed {len(rows)} certificate nodes in {replay_seconds:.3f}s",flush=True)
    rng=random.Random(20261020)
    samples=[]
    for trial in range(3):
        s=sample(rng)
        z={i:(F(rng.randint(-3,3)),F(rng.randint(1,4))) for i in range(1,5)}
        check=evaluator(s,z)
        for rule in data["rules"]:
            r=rows[rule["certificate"]]
            assert check(r)==0, ("catalog",trial,rule["head"],check(r))
        samples.append([str(s.m[i]) for i in range(1,5)])
        print(f"Exact rational sample {trial+1}: all {len(data['rules'])} rules passed",flush=True)
    report={
        "certificate_nodes_replayed":len(rows),
        "catalog_rules_verified":len(data["rules"]),
        "all_rule_heads_decreasing":True,
        "all_rows_same_external_representation":True,
        "reference_order_comparisons":1000,
        "exact_rational_polarized_samples":samples,
        "sample_check_scope":"Full covariant auxiliary-polarization evaluation, not highest-weight evaluation; finite checks are not generic proofs.",
        "certificate_replay_seconds":replay_seconds,
        "total_seconds":time.perf_counter()-start,
        "mathematica_started":False,
    }
    (out/"verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    from render_math_previews import render
    render([out/"worked_spairs.md"])
    print(json.dumps(report,indent=2),flush=True)


if __name__=="__main__":
    main()
