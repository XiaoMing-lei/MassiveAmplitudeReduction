"""Explicit manuscript inputs, exact certificates, and B' reduction timings."""
import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from statistics import median
from time import perf_counter

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
import verify_bounded_four_point as verify
from export_bounded_four_point import polynomial_tex,unit_tex


def grouped_tex(row, multiline=False):
    terms=[]
    for m,co in sorted(row.items(),key=lambda x:b.mkey(x[0]),reverse=True):
        factors=[];sign=1
        for u in m:
            d,kind,ll,cc=u
            if kind and d==2 and cc==(0,1):
                # In the recorded determinant convention Tr([ij]<ji>)=-s_ij.
                factors.append(r's_{'+''.join(map(str,ll))+'}');sign=-sign
            elif not kind and d>1:
                factors.append((r'\langle' if cc[0] else '[')+rf'\mathbf{{{ll[0]}}}|'+
                               r'\,'.join(rf'p_{{{i}}}' for i in ll[1:-1])+
                               rf'|\mathbf{{{ll[-1]}}}'+(r'\rangle' if cc[-1] else ']'))
            else:factors.append(unit_tex(u))
        co={e:sign*v for e,v in co.items()}
        tensor=r'\,'.join(factors)
        coefficient=polynomial_tex({():co})
        if not tensor:terms.append(coefficient)
        elif co==b.ONE:terms.append(tensor)
        elif co=={b.ZERO:-1}:terms.append('-'+tensor)
        else:terms.append(r'\left('+coefficient+r'\right)'+tensor)
    if multiline and len(terms)>2:
        lines=['+'.join(terms[i:i+2]).replace('+-','-') for i in range(0,len(terms),2)]
        return r'\begin{aligned}&'+('\\\\\n&+').join(lines).replace('&+-','&-')+r'\end{aligned}'
    return '+'.join(terms).replace('+-','-') or '0'


def inputs():
    def unit(i,j,c):return b.order.chain((i,j),(c,))
    v=b.mono((unit(1,2,1),unit(3,4,1),unit(1,3,0),unit(2,4,0)))
    f=b.mono((unit(1,2,1),unit(3,4,1),unit(3,4,0)))
    scalar=b.normalize_graph((1,4,4,1),((0,1,1),(2,3,0)),((1,2),(3,0)))
    def multiply(a,c):
        out={}
        for x,co in a.items():
            for y,cc in c.items():b.add_term(out,b.mono(x+y),b.pmul(co,cc))
        return out
    vv={v:b.ONE};ff={f:b.ONE}
    return {'TableII_V4_d6':multiply(vv,scalar),
            'TableII_psi2V2_d7':multiply(multiply(ff,scalar),scalar),
            'V4_d8_same_scalar_squared':multiply(multiply(vv,scalar),scalar)}


def short_inputs():
    def scalar(i,j):
        return b.normalize_graph((i,j,j,i),((0,1,1),(2,3,0)),((1,2),(3,0)))
    def mul(a,c):
        out={}
        for m,co in a.items():
            for n,cc in c.items():b.add_term(out,b.mono(m+n),b.pmul(co,cc))
        return out
    replacement={():b.mass(4,2,-2)}
    for pair in ((2,4),(3,4)):
        for m,co in scalar(*pair).items():b.add_term(replacement,m,{e:-v for e,v in co.items()})
    unit=lambda i,j,c:b.order.chain((i,j),(c,))
    v={b.mono((unit(1,2,1),unit(3,4,1),unit(1,3,0),unit(2,4,0))):b.ONE}
    f={b.mono((unit(1,2,1),unit(3,4,1),unit(3,4,0))):b.ONE}
    return {'TableII_V4_d6':mul(v,replacement),
            'TableII_psi2V2_d7':mul(mul(f,replacement),replacement),
            'V4_d8_same_scalar_squared':mul(mul(v,replacement),replacement)}


def validate_certificates(data):
    count=0
    for rec in data['parents']:
        if rec['raw'] is not None:continue
        source=rec['source'];head=verify.freeze(source['common_input'])
        left=bp.read_row(source['left_identity']);right=bp.read_row(source['right_identity'])
        assert max(left,key=b.mkey)==max(right,key=b.mkey)==head
        row=p.subtract(left,left[head],right,right[head])
        assert row==bp.read_row(source['S_polynomial'])
        if 'primitive_S_polynomial' in source:
            primitive=bp.read_row(source['primitive_S_polynomial'])
            factor=bp.freeze(source['S_common_factor'])
            scale={tuple(e):v for e,v in source['S_coefficient_scale']}
            assert row==bp.poly_scale(p.multiply(primitive,factor),scale)
            row=primitive
        for step in source['reduction_steps']:
            rel=bp.read_row(step['identity'])
            h=verify.freeze(step['input'])
            ah={tuple(e):v for e,v in step['input_coefficient']}
            rh={tuple(e):v for e,v in step['leading_coefficient']}
            assert row[h]==ah and rel[h]==rh
            assert max(rel,key=b.mkey)==h
            row=p.subtract(row,ah,rel,rh)
        expected=p.multiply(bp.read_row(rec['row']),verify.freeze(source['removed_product']))
        expected=bp.poly_scale(expected,{tuple(e):v for e,v in source['removed_scale']})
        assert row==expected
        count+=1
    return count


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--catalog',required=True)
    ap.add_argument('--alternative-order',action='store_true')
    ap.add_argument('--parents-only',action='store_true')
    args=ap.parse_args()
    path=Path(args.catalog)
    suffix=path.stem.removeprefix('catalog')
    data=json.loads(path.read_text())
    bp.configure(4,8)
    tick=perf_counter();certificates=validate_certificates(data);cert_seconds=perf_counter()-tick
    def new_engine():
        engine=bp.Reducer(4,8)
        for rec in data['parents']:
            if rec['raw'] is None:engine.add_parent(bp.read_row(rec['row']),rec['source'])
        if not args.parents_only:engine.load_cached_descendants(data.get('descendants',[]))
        return engine
    results=[]
    for name,row in inputs().items():
        tick=perf_counter();engine=new_engine();initialization=perf_counter()-tick
        tick=perf_counter();answer,den,steps=engine.reduce(row,trace=True)
        answer,den=bp.cancel_denominator(answer,den)
        cold=perf_counter()-tick
        times=[]
        for _ in range(5):
            tick=perf_counter();warm,wd,_=engine.reduce(row)
            warm,wd=bp.cancel_denominator(warm,wd);times.append(perf_counter()-tick)
            assert warm==answer and wd==den
        again,ad,_=engine.reduce(answer)
        idem=p.subtract(again,ad,answer,b.ONE)=={}
        record={'name':name,'input':row,'output_numerator':answer,'output_denominator':den,
                'input_terms':len(row),'output_terms':len(answer),'steps':steps,
                'cold_seconds':cold,'warm_seconds':times,'warm_median':median(times),
                'catalog_initialization_seconds':initialization,
                'saved_descendants_loaded':not args.parents_only,
                'idempotent':idem}
        record['all_output_monomials_irreducible']=all(not engine.actions(m) for m in answer)
        short=short_inputs()[name]
        short_answer,short_den,_=engine.reduce(short)
        record['previous_short_input']=short
        record['previous_short_terms']=len(short)
        record['short_reduces_to_identical_expression']=not p.subtract(answer,den,short_answer,short_den)
        record['short_monomials_reducible']=sum(bool(engine.actions(m,first_only=True)) for m in short)
        if args.alternative_order:
            other_engine=new_engine()
            tick=perf_counter();other,other_den,_=other_engine.reduce(row,reverse=True)
            other,other_den=bp.cancel_denominator(other,other_den)
            record['alternative_order_seconds']=perf_counter()-tick
            record['alternative_order_terms']=len(other)
            record['alternative_order_identical']=not p.subtract(answer,den,other,other_den)
            record['alternative_output']=other
            record['alternative_denominator']=other_den
        results.append(record)
        print(json.dumps({k:v for k,v in record.items() if k not in ('input','output_numerator','output_denominator','steps','previous_short_input','alternative_output','alternative_denominator')}),flush=True)
    tick=perf_counter();rng=random.Random(20261023);samples=[]
    for trial in range(3):
        spin=verify.sample(rng)
        z={i:(Fraction(rng.randint(-3,3)),Fraction(rng.randint(1,4))) for i in range(1,5)}
        evaluate=verify.evaluator(spin,z)
        for rec in data['parents']:
            assert evaluate(bp.read_row(rec['row']))==0,rec['id']
        for rec in results:
            dv=evaluate({():rec['output_denominator']})
            assert dv!=0
            assert evaluate(rec['input'])*dv==evaluate(rec['output_numerator']),rec['name']
        samples.append({'masses':[str(spin.m[i]) for i in range(1,5)],'all_catalog_and_benchmark_checks':True})
    report={'catalog':str(path),'catalog_status':data['summary']['status'],
            'replayed_S_certificates':certificates,'certificate_seconds':cert_seconds,
            'exact_samples':samples,'evaluation_seconds':perf_counter()-tick,
            'benchmarks':results,'no_basis_construction':True}
    bp.save(path.parent/('benchmarks'+suffix+'.json'),report)
    text=['# B′: explicit manuscript benchmark reductions\n',
          'Mass coefficients and scalar signs follow the manuscript sample code, with $s_{ij}=2p_i\\cdot p_j$. Outputs are reduced expressions; unrestricted uniqueness is not claimed.\n',
          '| Input | Terms | Cold seconds | Warm median seconds | Idempotent |\n|---|---:|---:|---:|---|']
    for r in results:text.append(f"| {r['name']} | {r['output_terms']} | {r['cold_seconds']:.6g} | {r['warm_median']:.6g} | {r['idempotent']} |")
    for r in results:
        den_tex=polynomial_tex({():r['output_denominator']})
        result=grouped_tex(r['output_numerator'],multiline=True)
        if r['output_denominator']!=b.ONE:result=r'\frac{'+result+'}{'+den_tex+'}'
        text+=['\n## '+r['name'],'\nInput:\n\n$$\n'+grouped_tex(r['input'])+'\n$$',
                '\nReduced expression:\n\n$$\n'+result+'\n$$']
    text.append(f'\nAll {certificates} saved S-polynomial derivation certificates replayed exactly. All parent identities and all benchmark equalities passed three exact rational on-shell polarized evaluations. Evaluation is validation only, never construction or selection.')
    (path.parent/('BENCHMARKS'+suffix+'.md')).write_text('\n'.join(text)+'\n',encoding='utf-8')
    print(json.dumps({'certificates':certificates,'exact_samples':3,'saved':str(path.parent/('BENCHMARKS'+suffix+'.md'))}),flush=True)


if __name__=='__main__':main()
