"""Independent saved-certificate, identity, and parent-only B2 checks."""
import argparse
import json
import random
from fractions import Fraction
from pathlib import Path
from time import perf_counter
import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_b2 import B2Reducer
from optimized_bprime import load_frozen
from benchmark_bprime import validate_certificates
from check_bprime_interreduced import replay
import verify_bounded_four_point as verify


def load_b2(data):
    engine=load_frozen(data)
    engine.__class__=B2Reducer
    return engine


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--catalog',required=True)
    args=ap.parse_args();path=Path(args.catalog)
    data=json.loads(path.read_text());n=data['summary']['particles'];d=data['summary']['degree']
    bp.configure(n,d);tick=perf_counter()
    count=validate_certificates({'parents':[{**r,'row':r.get('initial_row',r['row'])}
                                           for r in data['history_records']]})
    updates=0
    for event in data['journal']:
        if event['event']!='update':continue
        row,den=replay(bp.read_row(event['old_row']),event['reduction_steps'])
        expected=bp.poly_scale(p.multiply(bp.read_row(event['row']),bp.freeze(event['removed_product'])),
                              {tuple(e):v for e,v in event['removed_scale']})
        assert row==expected
        assert den=={tuple(e):v for e,v in event['denominator']}
        updates+=1
    e=load_b2(data);failures=[]
    for r in e.parents:
        if r['raw'] is not None or not r['active']:continue
        with e.without_parent(r['id']):
            actions=e.candidate_term_actions(r['row'])
            if actions:failures.append({'parent':r['id'],'actions':actions})
    old=json.loads(Path('tensor_rules/bprime/n4_d6_unique_momentum/catalog.json').read_text())
    oldfail=[];compared=0
    for r in old['parents']:
        row=bp.read_row(r['row'])
        if row and max(map(p.degree,row))>d:continue
        compared+=1
        ans,den,steps=e.reduce(row,trace=True)
        if ans:oldfail.append({'parent':r['id'],'input':row,'remainder':ans,'steps':steps})
    sextic=None
    if d>=6:
        target=json.loads(Path('tensor_rules/bprime/n4_d8_unique_momentum/record304_minimal_overlap_audit.json').read_text())
        row=bp.read_row(target['remainder']);key=p.encode(p.primitive(row)[0])
        exact=[r['id'] for r in e.parents if p.encode(p.primitive(r['row'])[0])==key]
        rem,den,steps=e.reduce(row,trace=True)
        sextic={'exact_parent_ids':exact,'remainder':rem,'steps':steps}
    rng=random.Random(2026102431)
    for trial in range(3):
        spin=verify.sample(rng)
        pol={i:(Fraction(rng.randint(-3,3)),Fraction(rng.randint(1,4))) for i in range(1,5)}
        evaluate=verify.evaluator(spin,pol)
        for r in e.parents:
            if r['active']:assert evaluate(r['row'])==0,r['id']
    report={'insertion_certificates':count,'update_certificates':updates,
        'generated_parents_with_reducible_terms':failures,
        'old_parents_compared':compared,'old_parent_nonzero_remainders':oldfail,
        'known_missing_sextic':sextic,'exact_physical_samples':3,
        'verification_seconds':perf_counter()-tick}
    bp.save(path.parent/'verification.json',report)
    print(json.dumps({'insertion_certificates':count,'update_certificates':updates,
        'reducible_parents':len(failures),'old_parent_failures':len(oldfail),
        'sextic_exact_ids':None if sextic is None else sextic['exact_parent_ids'],
        'sextic_remainder_terms':None if sextic is None else len(sextic['remainder']),
        'seconds':report['verification_seconds']}),flush=True)


if __name__=='__main__':main()
