"""Resumable overnight execution of the unchanged incremental-pool algorithm.

Only disposable memoization is bounded. Proofs, routes, completed pair versions
and unfinished S-polynomials are checkpointed at safe operation boundaries.
"""
import argparse
from collections import Counter
import ctypes
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import pickle
import shutil
import signal
from time import perf_counter
import traceback
import checkpoint_io
import construct_route_pool as c
from efficient_b2_restart import BoundedCache, CACHE_LIMITS, bound_function_caches


class Memo(BoundedCache):
    def pop(self,key,*default):
        if key in self:
            value=dict.__getitem__(self,key)
            self.__delitem__(key)
            return value
        if default:return default[0]
        raise KeyError(key)


def memory():
    if os.name!='nt':return {}
    class Status(ctypes.Structure):
        _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[
            (x,ctypes.c_ulonglong) for x in ('total','available','page_total','page_available','virtual_total','virtual_available','extended')]
    class Counters(ctypes.Structure):
        _fields_=[('cb',ctypes.c_ulong),('faults',ctypes.c_ulong)]+[
            (x,ctypes.c_size_t) for x in ('peak','rss','peak_paged','paged','peak_nonpaged','nonpaged','pagefile','peak_pagefile','private')]
    s=Status();s.length=ctypes.sizeof(s);ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(s))
    q=Counters();q.cb=ctypes.sizeof(q)
    ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(-1),ctypes.byref(q),q.cb)
    return {'physical_total_bytes':s.total,'physical_available_bytes':s.available,
            'process_rss_bytes':q.rss,'process_private_bytes':q.private}


def atomic_json(path,value):
    temporary=path.with_suffix(path.suffix+'.tmp')
    with temporary.open('w',encoding='utf8') as stream:
        json.dump(c.bp.serial(value),stream,separators=(',',':'));stream.flush();os.fsync(stream.fileno())
    os.replace(temporary,path)


DISPOSABLE=set(CACHE_LIMITS)|{'_original_blocks','_pattern_index','_derived_terms'}
TRANSIENT={'engine','direct_cache','start','next_progress','next_control','last_save','last_progress',
           'next_resource_check','next_checkpoint','saving','pause_reason','memory_state','deferred_remainders'}


class Overnight(c.RoutePoolConstruction):
    def __init__(self,n,degree,out,interval=1800,memo_limit=50000):
        super().__init__(n,degree,out)
        self.interval=interval;self.memo_limit=memo_limit;self.generation=0
        self.completed_stage=1;self.phase='degree_stages';self.pause_reason=None
        self.saving=False;self.next_checkpoint=perf_counter()+interval
        self.next_resource_check=perf_counter()+10;self.memory_state=memory()
        self.report_options.update(checkpoint_interval_seconds=interval,
            checkpoint_format='Atomic complete state; last two generations retained',
            algorithm_unchanged_from='construct_route_pool.py',
            disposable_memoization_limit=memo_limit,
            internal_checks_seconds_separate=True)
        self.bound_memos();bound_function_caches()

    def bound_memos(self):
        if not isinstance(self.direct_cache,Memo):self.direct_cache=Memo(self.memo_limit,self.direct_cache)
        for name,limit in CACHE_LIMITS.items():
            value=getattr(self.engine,name,{})
            if not isinstance(value,Memo):setattr(self.engine,name,Memo(min(limit,self.memo_limit),value))

    def report(self,status):
        active=[r for r in self.engine.parents if r['active']]
        elapsed=self.prior_seconds+perf_counter()-self.start
        return {**self.report_options,'particles':self.n,'degree':self.degree,'status':status,
            'utc':datetime.now(timezone.utc).isoformat(),'pid':os.getpid(),'stage':self.stage,
            'phase':self.phase,'completed_degree_stage':self.completed_stage,
            'parents':len(active),'originals':sum(r['raw'] is not None for r in active),
            'historical_parent_records':len(self.engine.parents),
            'parent_degrees':dict(Counter(max(map(c.p.degree,r['row']),default=2) for r in active)),
            'seconds':elapsed,'cumulative_construction_seconds':elapsed,
            'construction_compute_seconds':elapsed-self.timings['checkpoint_io_seconds'],
            'timings':dict(self.timings),'stats':dict(self.stats),'reducer_stats':dict(self.engine.stats),
            'queued_S_polynomials':len(self.s_heap),'pending_parent_pairs':len(self.pair_heap),
            'deferred_above_bound_S_polynomials':sum(len(v) for v in self.blocked.values()),
            'pools':len(self.pools),'routes':len(self.routes),'route_connections':len(self.route_edges),
            'memory':self.memory_state,'pause_reason':self.pause_reason,'checkpoint_generation':self.generation,
            'no_basis_enumeration':True,'raw_parent_count_not_proved_independent':True}

    def control(self):
        now=perf_counter()
        if now<self.next_control:return
        self.next_control=now+0.5
        path=self.out/'control.json'
        if path.exists():
            action=json.loads(path.read_text()).get('action')
            if action=='pause':self.pause_reason='User/control pause requested'
            if action=='checkpoint':self.next_checkpoint=0
        if now>=self.next_resource_check:
            self.next_resource_check=now+30;self.memory_state=memory()
            total=self.memory_state.get('physical_total_bytes',0)
            if total and (self.memory_state['process_private_bytes']>0.65*total or
                          self.memory_state['physical_available_bytes']<max(1_000_000_000,0.08*total)):
                self.pause_reason='Resource guard: save before memory pressure becomes unsafe'
        if now>=self.next_progress:
            self.next_progress=now+60
            report=self.report('running');atomic_json(self.out/'progress.json',report)
            with (self.out/'progress_history.jsonl').open('a',encoding='utf8') as stream:
                stream.write(json.dumps(c.bp.serial(report),separators=(',',':'))+'\n')

    def boundary(self):
        self.bound_memos()
        if self.pause_reason:
            self.checkpoint('paused_partial',self.stage)
            raise InterruptedError(self.pause_reason)
        if perf_counter()>=self.next_checkpoint:
            self.checkpoint('running_checkpoint',self.stage)
            path=self.out/'control.json'
            if path.exists() and json.loads(path.read_text()).get('action')=='checkpoint':
                atomic_json(path,{'action':'continue'})

    def process_pair(self,item):
        super().process_pair(item);self.boundary()

    def process_task(self,item):
        super().process_task(item);self.boundary()

    def checkpoint(self,status,stage,full=True):
        self.stage=stage
        if not full:
            report=self.report(status);atomic_json(self.out/'progress.json',report);return report
        assert self.current_pair is None and self.current_task is None,'Save only at an operation boundary'
        self.saving=True;tick=perf_counter();self.generation+=1
        directory=self.out/f'checkpoint-{self.generation:06d}'
        temporary=self.out/f'checkpoint-{self.generation:06d}.partial';temporary.mkdir()
        state={k:v for k,v in vars(self).items() if k not in TRANSIENT}
        engine={k:v for k,v in vars(self.engine).items() if k not in DISPOSABLE and not callable(v)}
        state['prior_seconds']=self.prior_seconds+perf_counter()-self.start
        with gzip.open(temporary/'state.pkl.gz','wb',compresslevel=1) as stream:
            pickle.dump({'task':state,'engine':engine},stream,protocol=5)
        report=self.report(status)
        catalog={'summary':report,'parents':[r for r in self.engine.parents if r['active']],
            'history_records':self.engine.parents,'journal':self.engine.journal,
            'full_search_archive':None,'checkpoint_state':'state.pkl.gz'}
        atomic_json(temporary/'catalog.json',catalog)
        os.replace(temporary,directory)
        self.timings['checkpoint_io_seconds']+=perf_counter()-tick
        report=self.report(status)
        manifest={'generation':self.generation,'directory':str(directory.resolve()),
            'state':str((directory/'state.pkl.gz').resolve()),'catalog':str((directory/'catalog.json').resolve()),
            'status':status,'utc':report['utc'],'seconds':report['seconds'],'timings':dict(self.timings),
            'state_bytes':(directory/'state.pkl.gz').stat().st_size}
        atomic_json(self.out/'latest_checkpoint.json',manifest)
        atomic_json(self.out/'progress.json',report)
        if status in ('degree_stage_finished','completed_degree_queue_and_encountered_contexts','paused_partial'):
            shutil.copyfile(directory/'catalog.json',self.out/'catalog.json')
        # These are this runner's two exact generated files, inside its output.
        olddir=self.out/f'checkpoint-{self.generation-2:06d}'
        if olddir.is_dir() and olddir.resolve().parent==self.out.resolve():
            for name in ('state.pkl.gz','catalog.json'):
                file=olddir/name
                if file.is_file():file.unlink()
            olddir.rmdir()
        self.last_save=perf_counter();self.next_checkpoint=self.last_save+self.interval;self.saving=False
        print(json.dumps({k:report[k] for k in ('status','stage','seconds','parents','parent_degrees','memory')}),flush=True)
        return report

    @classmethod
    def restore(cls,out):
        manifest=json.loads((out/'latest_checkpoint.json').read_text());tick=perf_counter()
        saved=checkpoint_io.load(manifest['state'])
        state=saved['task'];obj=cls(state['n'],state['degree'],out,state['interval'],state['memo_limit'])
        vars(obj).update(state);obj.out=out
        obj.engine=c.old.QueueReducer(obj.n,obj.degree)
        vars(obj.engine).update(saved['engine'])
        obj.engine.budget_check=obj.control;obj.engine.presentation_event=obj.presentation_event
        c.base.old.configure(obj.n,2*obj.degree)
        obj.prior_seconds=manifest['seconds'];obj.timings=Counter(manifest['timings'])
        obj.generation=manifest['generation'];obj.start=perf_counter()
        obj.pause_reason=None;obj.next_control=0;obj.next_progress=obj.start+60
        obj.next_resource_check=obj.start+10;obj.next_checkpoint=obj.start+obj.interval
        obj.direct_cache=Memo(obj.memo_limit);obj.bound_memos()
        obj.memory_state=memory();obj.timings['resume_loading_seconds']+=perf_counter()-tick
        assert obj.current_pair is None and obj.current_task is None
        return obj

    def run(self):
        if self.phase=='degree_stages':
            for stage in range(self.completed_stage+1,self.degree+1):
                tick=perf_counter();self.stabilize(stage)
                self.rounds.append({'parent_degree':stage,'seconds_this_segment':perf_counter()-tick,
                    'active_parents':sum(r['active'] for r in self.engine.parents),
                    'provisional_while_higher_S_polynomials_pending':True})
                self.completed_stage=stage
                self.checkpoint('degree_stage_finished',{'parent_degree':stage})
                if stage in (6,8):
                    target=self.out/f'candidate_checks_d{stage}';target.mkdir(exist_ok=True)
                    if not (target/'catalog.json').exists():shutil.copyfile(self.out/'catalog.json',target/'catalog.json')
            self.phase='above_bound_queue'
        if self.phase=='above_bound_queue':
            self.stabilize(self.degree,allow_higher=True);self.phase='context_preparation'
        if self.phase=='context_preparation':
            for attempt in range(1,21):
                self.stage={'parent_degree':self.degree,'phase':'context_preparation','pass':attempt}
                version=self.engine.version;before=len(self.tasks);tick=perf_counter()
                self.prepare_contexts();self.timings['context_preparation_seconds']+=perf_counter()-tick
                self.stabilize(self.degree,allow_higher=True);self.boundary()
                if self.engine.version==version and len(self.tasks)==before:break
            else:raise RuntimeError('Context preparation did not stabilize')
            c.bp.save(self.out/'final_groups.json',[{'id':r['id'],'family':r['family'],
                'original':r['raw'] is not None,'group':c.old.prior.rule_group(r['row']) if r['row'] else 2,
                'degree':max(map(c.p.degree,r['row']),default=2)} for r in self.engine.parents if r['active']])
            self.phase='complete'
        return self.checkpoint('completed_degree_queue_and_encountered_contexts',{'parent_degree':self.degree})


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--particles',type=int,default=4)
    ap.add_argument('--degree',type=int,default=8);ap.add_argument('--out',required=True)
    ap.add_argument('--resume',action='store_true');ap.add_argument('--interval',type=float,default=1800)
    ap.add_argument('--memo-limit',type=int,default=50000)
    args=ap.parse_args();out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=args.resume)
    control=out/'control.json'
    if control.exists() and json.loads(control.read_text()).get('action')=='pause':raise RuntimeError('Clear the acknowledged pause request before resuming')
    lock=out/'run.lock'
    with lock.open('x') as stream:stream.write(str(os.getpid()))
    task=None
    try:
        task=Overnight.restore(out) if args.resume else Overnight(args.particles,args.degree,out,args.interval,args.memo_limit)
        if task.phase=='complete':raise RuntimeError('This construction is already complete')
        atomic_json(out/'process.json',{'pid':os.getpid(),'status':'running','entrypoint':str(Path(__file__).resolve()),'resume':args.resume})
        source=out/'source_snapshot';source.mkdir(exist_ok=True)
        hashes={}
        for file in Path(__file__).parent.glob('*.py'):
            target=source/file.name
            if not target.exists():shutil.copyfile(file,target)
            hashes[file.name]=hashlib.sha256(file.read_bytes()).hexdigest()
        atomic_json(out/'source_hashes.json',hashes)
        def pause(signum,frame):task.pause_reason=f'Signal {signum}: pause at next safe boundary'
        signal.signal(signal.SIGINT,pause);signal.signal(signal.SIGTERM,pause)
        task.run();atomic_json(out/'process.json',{'pid':os.getpid(),'status':'construction_complete_validation_pending'})
    except InterruptedError as error:
        atomic_json(out/'process.json',{'pid':os.getpid(),'status':'paused','reason':str(error)})
    except BaseException as error:
        (out/'error.txt').write_text(traceback.format_exc(),encoding='utf8')
        atomic_json(out/'process.json',{'pid':os.getpid(),'status':'error','reason':repr(error)})
        raise
    finally:
        if lock.exists():lock.unlink()


if __name__=='__main__':main()
