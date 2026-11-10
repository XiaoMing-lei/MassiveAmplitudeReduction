"""Export bold-bracket rules and executable finite normal-form tables."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
import time
import build_bounded_four_point as b
from verify_bounded_four_point import freeze, decode_row


def unit_tex(u):
    d,kind,ll,cc=u
    bold=lambda i:rf"\mathbf{{{i}}}"
    if kind:
        terms=[]
        for j,c in enumerate(cc):
            pair=bold(ll[j])+r"\,"+bold(ll[(j+1)%len(ll)])
            terms.append(r"\langle"+pair+r"\rangle" if c else "["+pair+"]")
        return r"\operatorname{Tr}\!\left("+ "".join(terms)+r"\right)"
    if d==1:
        pair=bold(ll[0])+r"\,"+bold(ll[-1])
        return r"\langle"+pair+r"\rangle" if cc[0] else "["+pair+"]"
    return ((r"\langle" if cc[0] else "[")+bold(ll[0])+"|"+
            r"\,".join(bold(i) for i in ll[1:-1])+"|"+bold(ll[-1])+
            (r"\rangle" if cc[-1] else "]"))


def polynomial_tex(row):
    pieces=[]
    for mon,co in sorted(row.items(),key=lambda kv:b.mkey(kv[0]),reverse=True):
        for e,c in sorted(co.items(),reverse=True):
            if not c:
                continue
            factors=[]
            if abs(c)!=1 or (not mon and not any(e)):
                factors.append(str(abs(c)))
            factors.extend("m_{"+str(i)+"}"+("^"+str(k) if k>1 else "")
                           for i,k in enumerate(e,1) if k)
            factors.extend(unit_tex(u) for u in mon)
            term=r"\,".join(factors)
            pieces.append(("-" if c<0 else "+" if pieces else "")+term)
    return "".join(pieces) or "0"


def main():
    start=time.perf_counter()
    out=Path(__file__).parent/"bounded_n4_d4"
    data=json.loads((out/"catalog.json").read_text(encoding="utf-8"))
    mons=[freeze(m) for m in data["monomials"]]
    ids={m:i for i,m in enumerate(mons)}
    basis={mons[r["head"]]:decode_row(r["row"],mons) for r in data["rules"]}
    assert all(row[h]==b.ONE for h,row in basis.items())

    @lru_cache(None)
    def nf(m):
        if m not in basis:
            return {m:b.ONE}
        outrow={}
        for t,co in basis[m].items():
            if t==m:
                continue
            for u,p in nf(t).items():
                b.add_term(outrow,u,{e:-c for e,c in b.pmul(co,p).items()})
        return outrow

    def divisor(h):
        for size in range(1,len(h)):
            for positions in combinations(range(len(h)),size):
                chosen=tuple(h[i] for i in positions)
                if chosen in basis:
                    return chosen
        return None
    primitive=[h for h in basis if divisor(h) is None]
    primitive_set=set(primitive)

    @lru_cache(None)
    def compact_nf(m):
        chosen=None
        for size in range(1,len(m)+1):
            for pos in combinations(range(len(m)),size):
                part=tuple(m[i] for i in pos)
                if part in primitive_set:
                    chosen=part
                    break
            if chosen is not None:
                break
        if chosen is None:
            return {m:b.ONE}
        remainder=list(m)
        for u in chosen:
            remainder.remove(u)
        outrow={}
        for t,co in nf(chosen).items():
            target=b.mono(t+tuple(remainder))
            assert b.mkey(target)<b.mkey(m)
            for u,p in compact_nf(target).items():
                b.add_term(outrow,u,b.pmul(co,p))
        return outrow

    for m in mons:
        assert compact_nf(m)==nf(m)
    def raw_term(specs,coeff):
        row={():coeff}
        for labels,colors in specs:
            nxt={}
            for m,c in row.items():
                for u,p in b.normalize_unit(0,tuple(labels),tuple(colors)).items():
                    b.add_term(nxt,b.mono(m+u),b.pmul(c,p))
            row=nxt
        return row
    def reduce_row(row):
        outrow={}
        for m,c in row.items():
            for t,p in compact_nf(m).items():
                b.add_term(outrow,t,b.pmul(c,p))
        return outrow
    cubic={}
    for specs,c in [
        ([([1,4],[0]),([2,4,3],[0,1])],b.ONE),
        ([([1,2],[0]),([4,2,3],[0,1])],{b.ZERO:-1}),
        ([([1,2],[0]),([3,4],[1])],b.mass(4,sign=-1)),
        ([([1,4],[0]),([2,3],[1])],b.mass(2,sign=-1)),
        ([([1,3],[0]),([2,4],[0])],b.mass(3,sign=-1)),
        ([([2,4],[0]),([1,3],[1])],b.mass(1,sign=-1)),
    ]:
        for m,c in raw_term(specs,c).items():
            b.add_term(cubic,m,c)
    assert not reduce_row(cubic)
    cubic_head=max(cubic,key=b.mkey)
    for r in (1,2,3):
        # Canonical angle factor has endpoint 4 in its second slot.
        factor=b.order.chain([r,4],[1])
        attached=dict(b.contexts(cubic,cubic_head,factor))[2]
        assert not reduce_row(attached)
    fullnfs={ids[h]:b.serial_row(nf(h),ids) for h in basis}
    # Every tensor-product-subsumed rule is checked against the complete NF.
    for h in basis:
        div=divisor(h)
        if div is None:
            continue
        residual=list(h)
        for u in div:
            residual.remove(u)
        expected={}
        for t,co in nf(div).items():
            for u,p in nf(b.mono(t+tuple(residual))).items():
                b.add_term(expected,u,b.pmul(co,p))
        assert expected==nf(h)
    (out/"normal_forms.json").write_text(json.dumps({
        "description":"Monic normal-form table for the bounded relation span. IDs refer to catalog.json.",
        "normal_forms":fullnfs,
        "tensor_product_primitive_heads":[ids[h] for h in primitive]
    },separators=(",",":"))+"\n",encoding="utf-8")
    bysector=Counter(map(b.sector,mons))
    pivots=Counter(map(b.sector,basis))
    degrees=Counter(sum(u[0] for u in h) for h in primitive)
    for degree in (2,3,4):
        text=[f"# Degree-{degree} rules after tensor-product subsumption\n",
              "All particle labels are fixed at n=4. These are monic rules with fully reduced tails.",
              "Products of lower rules have been omitted, with NF equivalence checked. Contraction subsumption has not been used.",
              "Trace notation and mass signs follow FourPointContextualSPairs.md.\n"]
        for h in sorted(primitive,key=b.mkey,reverse=True):
            if sum(u[0] for u in h)!=degree:
                continue
            text.extend([f"## Head {ids[h]}; free-slot counts {b.sector(h)}\n",
                         "$$\n"+polynomial_tex({h:b.ONE})+
                         "\\longrightarrow\n"+polynomial_tex(nf(h))+"\n$$\n"])
        (out/f"rules_degree_{degree}.md").write_text("\n\n".join(text)+"\n",encoding="utf-8")
    table=["# All external-representation sectors\n",
           "Free-slot counts are twice the external spins. Standard monomial counts refer only to this bounded relation span.\n",
           "| Free-slot counts | Monomials | Pivot rules | Standard monomials |",
           "|---|---:|---:|---:|"]
    for s,n in sorted(bysector.items()):
        table.append(f"| {s} | {n} | {pivots[s]} | {n-pivots[s]} |")
    (out/"representation_sectors.md").write_text("\n".join(table)+"\n",encoding="utf-8")
    report={
        "monic_rules":len(basis),
        "tensor_product_primitive_rules":len(primitive),
        "primitive_rules_by_degree":dict(degrees),
        "tensor_product_subsumption_checks":len(basis)-len(primitive),
        "compact_catalog_NF_agreement_checks":len(mons),
        "previous_cubic_and_three_reversed_descendants_reduce_to_zero":True,
        "standard_monomials_in_bounded_span":len(mons)-len(basis),
        "scalar_standard_monomials":bysector[(0,0,0,0)]-pivots[(0,0,0,0)],
        "largest_normal_form_terms":max(len(nf(h)) for h in basis),
        "seconds":time.perf_counter()-start,
    }
    (out/"export_report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    from render_math_previews import render
    render([out/f"rules_degree_{d}.md" for d in (2,3,4)])
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    main()
