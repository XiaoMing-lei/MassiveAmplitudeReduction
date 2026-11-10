"""Audit versioned rule generation, backward updates, and final reductions."""
import argparse
from collections import Counter
import json
from pathlib import Path
from time import perf_counter
import random
from fractions import Fraction
import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from construct_bprime_interreduced import VersionedReducer
from benchmark_bprime import validate_certificates
import verify_bounded_four_point as verify


def replay(row,steps):
    den=b.ONE
    for step in steps:
        rel=bp.read_row(step['identity']);head=bp.freeze(step['input'])
        ah={tuple(e):v for e,v in step['input_coefficient']}
        rh={tuple(e):v for e,v in step['leading_coefficient']}
        assert max(rel,key=b.mkey)==head and row[head]==ah and rel[head]==rh
        row=p.subtract(row,ah,rel,rh);den=b.pmul(den,rh)
    return row,den


def load_engine(data):
    engine=VersionedReducer(data['summary']['particles'],data['summary']['degree'],
                            unique_momentum_lm=data['summary'].get('unique_momentum_lm',False))
    for rec in data['history_records']:
        if rec['raw'] is not None:continue
        engine.add_parent(bp.read_row(rec['initial_row']),rec['source'])
        engine.parents[-1]['row']=bp.read_row(rec['row'])
        engine.parents[-1]['active']=rec['active']
        engine.parents[-1]['revision']=rec['revision']
    # Rebuild indexes using the final presentations, preserving stable IDs.
    engine.derived_patterns=[];engine.cache.clear();engine.cache_encodings.clear();engine.action_cache={}
    for rec in engine.parents:
        if rec['raw'] is not None or not rec['active']:continue
        for ti,pattern in engine.parent_patterns(rec):
            ll,bb,ee=pattern;signature=Counter((c,tuple(sorted((ll[a],ll[z])))) for a,z,c in bb)
            engine.derived_patterns.append((rec['id'],ti,pattern,signature))
        head=max(rec['row'],key=b.mkey)
        engine.cache[head].append((rec['row'],{'parent':rec['id'],'kind':'derived-product'}))
        engine.cache_encodings[head].add(p.encode(rec['row']))
    return engine


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--catalog',default='tensor_rules/bprime/n4_d4_interreduced/catalog.json')
    args=ap.parse_args();path=Path(args.catalog);data=json.loads(path.read_text())
    n=data['summary']['particles'];degree=data['summary']['degree'];bp.configure(n,degree)
    tick=perf_counter();initial={'parents':[{**r,'row':r.get('initial_row',r['row'])} for r in data['history_records']]}
    generation=validate_certificates(initial)
    state={r['id']:(0,bp.read_row(r['row'])) for r in data['history_records'] if r['raw'] is not None}
    updates=0
    for event in data['journal']:
        pid=event['parent']
        if event['event']=='insert':
            assert pid not in state;state[pid]=(0,bp.read_row(event['row']));continue
        revision,row=state[pid]
        assert revision+1==event['revision'] and row==bp.read_row(event['old_row'])
        result,den=replay(row,event['reduction_steps'])
        expected=bp.poly_scale(p.multiply(bp.read_row(event['row']),bp.freeze(event['removed_product'])),
                               {tuple(e):v for e,v in event['removed_scale']})
        assert result==expected
        assert den=={tuple(e):v for e,v in event['denominator']}
        for step in event['reduction_steps']:
            sid=step['source']['parent'];version=step['source'].get('parent_revision',0)
            assert sid!=pid and sid in state and version==state[sid][0],(pid,sid,version,state.get(sid))
        state[pid]=(event['revision'],bp.read_row(event['row']));updates+=1
    for rec in data['history_records']:assert state[rec['id']]==(rec['revision'],bp.read_row(rec['row']))
    proof_seconds=perf_counter()-tick
    engine=load_engine(data);tick=perf_counter();failures=[];terms=0
    for rec in engine.parents:
        if rec['raw'] is not None or not rec['active']:continue
        with engine.without_parent(rec['id']):
            actions=engine.candidate_term_actions(rec['row'])
            if actions:failures.append({'parent':rec['id'],'reducible_terms':actions})
            terms+=len(rec['row'])
    final_check_seconds=perf_counter()-tick
    assert not failures,[(x['parent'],len(x['reducible_terms'])) for x in failures]
    # Historical catalogs and original context instances are verification inputs.
    old=json.loads((path.parent.parent/'n4_d4_final/catalog.json').read_text())
    reference=json.loads((Path(__file__).parent/'originals_preserved_n4_d4/construction_d4.json').read_text())
    tick=perf_counter();reference_fail=[]
    for i,rec in enumerate(reference['instances']):
        answer,den,steps=engine.reduce(bp.read_row(rec['row']))
        if answer:reference_fail.append(i)
    historical_fail=[]
    for rec in old['parents']:
        if engine.reduce(bp.read_row(rec['row']))[0]:historical_fail.append(rec['id'])
    reference_seconds=perf_counter()-tick
    assert not reference_fail and not historical_fail,(reference_fail,historical_fail)
    reciprocal=None
    if degree==4:
        old_engine=bp.Reducer(4,4)
        for rec in old['parents']:
            if rec['raw'] is None:old_engine.add_parent(bp.read_row(rec['row']),rec['source'])
        reciprocal=all(not old_engine.reduce(bp.read_row(r['row']))[0] for r in data['parents'])
        assert reciprocal
    rng=random.Random(2026102318);tick=perf_counter()
    for trial in range(3):
        spin=verify.sample(rng);pol={i:(Fraction(rng.randint(-3,3)),Fraction(rng.randint(1,4))) for i in range(1,5)}
        evaluate=verify.evaluator(spin,pol)
        for rec in data['parents']:assert evaluate(bp.read_row(rec['row']))==0,rec['id']
    report={'generation_certificates_replayed':generation,'backward_update_certificates_replayed':updates,
            'final_additional_identities':len(data['parents'])-54,'final_terms_checked_against_other_rules':terms,
            'reducible_terms':0,'reference_contexts':len(reference['instances']),'reference_failures':[],
            'historical_parent_identities_reduce_to_zero':len(old['parents']),
            'all_current_identities_reduce_to_zero_with_historical_rules':reciprocal,
            'exact_massive_spinor_samples':3,'proof_seconds':proof_seconds,
            'final_term_audit_seconds':final_check_seconds,'reference_seconds':reference_seconds,
            'evaluation_seconds':perf_counter()-tick,'component_evaluation_only_for_validation':True}
    bp.save(path.parent/'verification.json',report);print(json.dumps(report),flush=True)


if __name__=='__main__':main()
