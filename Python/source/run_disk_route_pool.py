"""Overnight runner with lossless, operation-boundary disk-backed records.

The algebra and queue ordering are inherited unchanged. This is a storage
repair, not an overlap pruning or rule-construction change.
"""
import argparse
from collections import Counter
import gc
import gzip
import json
import os
from pathlib import Path
import pickle
import shutil
import signal
from time import perf_counter
import traceback
import run_route_pool_overnight as original
import durable_route_storage as disk

c = original.c


class DiskOvernight(original.Overnight):
    def cache_rechecks(self):
        """Identical cached-route propagation, with safe storage-only flushes.

        The complete new-row list is determined before propagation, as in the
        baseline. Never checkpoint mid-pass: its affected-input result still
        has to be consumed by stabilize().
        """
        new=[]
        for head,records in list(self.engine.cache.items()):
            for row,source in list(records):
                key=(head,c.p.encode(row))
                if key not in self.known_cache_polynomials:
                    self.known_cache_polynomials.add(key);new.append((head,row,source))
        affected=set();visited=0
        for ordinal,(head,row,source) in enumerate(new):
            if not head:continue
            unit=min(set(head),key=lambda u:len(self.input_postings.get(u,())))
            for mon in list(self.input_postings.get(unit,())):
                rest=c.p.quotient(mon,head)
                if rest is None:continue
                affected.add(mon)
                for flag in (False,True):self.engine.action_cache.pop((self.engine.version,mon,flag),None)
                if mon in self.pools:
                    self.register_route(mon,c.p.multiply(row,rest),source,
                        {'known_cached_product':True,'cached_head':head,'untouched_factor':rest})
                visited+=1
                if visited%128==0:
                    tick=perf_counter();self.disk_store.flush()
                    self.timings['record_storage_seconds']+=perf_counter()-tick
                    self.stage={'parent_degree':self.window,'phase':'cached_route_propagation',
                        'cached_source_index':ordinal,'cached_source_count':len(new),
                        'visited_divisible_inputs':visited}
                    self.control()
        tick=perf_counter();self.disk_store.flush()
        self.timings['record_storage_seconds']+=perf_counter()-tick
        self.stats['known_cached_routes_propagated']+=len(affected)
        return affected

    def install_store(self, migrate=False):
        tick = perf_counter()
        disk.attach(self, self.out/'working_records.sqlite3', migrate=migrate)
        self.timings['storage_migration_seconds'] += perf_counter()-tick
        self.report_options.update(storage='Exact compressed records in SQLite; mutable values pinned until safe boundary',
            algorithm_unchanged_from='construct_route_pool.py', storage_format_version=2)

    def boundary(self):
        if hasattr(self, 'disk_store'):
            tick = perf_counter(); self.disk_store.flush()
            self.timings['record_storage_seconds'] += perf_counter()-tick
        super().boundary()

    def report(self, status):
        result = super().report(status)
        # One-time conversion is maintenance, not rule construction. Keep the
        # raw execution clock for restart accounting and expose both scopes.
        maintenance=self.timings['storage_migration_seconds']
        result['active_execution_seconds']=result['seconds']
        result['storage_maintenance_seconds']=maintenance
        result['cumulative_construction_seconds']=result['seconds']-maintenance
        result['construction_compute_seconds']=result['seconds']-maintenance-self.timings['checkpoint_io_seconds']
        if hasattr(self,'disk_store'):
            result['record_store_bytes'] = self.disk_store.path.stat().st_size
            result['record_store_flushes'] = self.disk_store.flushes
        return result

    def checkpoint(self, status, stage, full=True):
        if not full or not hasattr(self,'disk_store'):
            return super().checkpoint(status,stage,full)
        self.stage=stage
        assert self.current_pair is None and self.current_task is None
        self.saving=True; tick=perf_counter(); self.generation+=1
        directory=self.out/f'checkpoint-{self.generation:06d}'
        temporary=self.out/f'checkpoint-{self.generation:06d}.partial'; temporary.mkdir()
        self.disk_store.backup(temporary/'records.sqlite3')
        state={k:(v.descriptor() if k in disk.FIELDS else v) for k,v in vars(self).items()
               if k not in original.TRANSIENT and k!='disk_store'}
        engine={k:v for k,v in vars(self.engine).items() if k not in original.DISPOSABLE and not callable(v)}
        state['prior_seconds']=self.prior_seconds+perf_counter()-self.start
        with gzip.open(temporary/'state.pkl.gz','wb',compresslevel=1) as stream:
            pickle.dump({'task':state,'engine':engine},stream,protocol=5)
        report=self.report(status)
        original.atomic_json(temporary/'catalog.json',{'summary':report,
            'parents':[r for r in self.engine.parents if r['active']],
            'history_records':self.engine.parents,'journal':self.engine.journal,
            'full_search_archive':None,'checkpoint_state':'state.pkl.gz',
            'route_storage':'records.sqlite3'})
        os.replace(temporary,directory)
        self.timings['checkpoint_io_seconds']+=perf_counter()-tick
        self.memory_state=original.memory(); report=self.report(status)
        manifest={'generation':self.generation,'directory':str(directory.resolve()),
            'state':str((directory/'state.pkl.gz').resolve()),
            'records':str((directory/'records.sqlite3').resolve()),
            'catalog':str((directory/'catalog.json').resolve()),'storage_format_version':2,
            'status':status,'utc':report['utc'],'seconds':report['seconds'],'timings':dict(self.timings),
            'state_bytes':(directory/'state.pkl.gz').stat().st_size,
            'record_bytes':(directory/'records.sqlite3').stat().st_size}
        original.atomic_json(self.out/'latest_checkpoint.json',manifest)
        original.atomic_json(self.out/'progress.json',report)
        if status in ('degree_stage_finished','completed_degree_queue_and_encountered_contexts','completed_capped_parent_queue','paused_partial','storage_migrated_verified'):
            shutil.copyfile(directory/'catalog.json',self.out/'catalog.json')
        # Preserve the pre-repair checkpoint 4. Other generations use last-two retention.
        olddir=self.out/f'checkpoint-{self.generation-2:06d}'
        protected=getattr(self,'protected_checkpoint_generations',(4,))
        if self.generation-2 not in protected and olddir.is_dir() and olddir.resolve().parent==self.out.resolve():
            try:
                for name in ('state.pkl.gz','catalog.json','records.sqlite3',
                             'records.sqlite3-wal','records.sqlite3-shm'):
                    file=olddir/name
                    if file.is_file():file.unlink()
                olddir.rmdir()
            except OSError as error:
                # A committed new checkpoint remains valid if optional old
                # generation cleanup is blocked. Never delete unknown files.
                original.atomic_json(self.out/'retention_warning.json',
                    {'committed_generation':self.generation,'old_directory':str(olddir),
                     'cleanup_error':repr(error),'new_checkpoint_valid':True})
        self.last_save=perf_counter();self.next_checkpoint=self.last_save+self.interval;self.saving=False
        print(json.dumps({k:report[k] for k in ('status','stage','seconds','parents','parent_degrees','memory')}),flush=True)
        return report

    @classmethod
    def restore(cls,out):
        manifest=json.loads((out/'latest_checkpoint.json').read_text())
        if 'records' in manifest:
            work=out/'working_records.sqlite3'
            # This runner owns these precise disposable working copies. The
            # committed checkpoint database remains untouched and recoverable.
            for suffix in ('','-wal','-shm'):
                file=Path(str(work)+suffix)
                if file.exists():file.unlink()
            shutil.copyfile(manifest['records'],work)
        task=super().restore(out)
        task.install_store(migrate='records' not in manifest)
        gc.collect()
        task.memory_state=original.memory()
        return task


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True)
    ap.add_argument('--particles',type=int,default=4);ap.add_argument('--degree',type=int,default=8)
    ap.add_argument('--resume',action='store_true');ap.add_argument('--migrate-only',action='store_true')
    ap.add_argument('--interval',type=float,default=1800);ap.add_argument('--memo-limit',type=int,default=20000)
    args=ap.parse_args();out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=args.resume)
    control=out/'control.json'
    if control.exists() and json.loads(control.read_text()).get('action')=='pause':
        raise RuntimeError('Clear an acknowledged pause request before resuming')
    lock=out/'run.lock'
    with lock.open('x') as stream:stream.write(str(os.getpid()))
    task=None
    try:
        task=DiskOvernight.restore(out) if args.resume else DiskOvernight(args.particles,args.degree,out,args.interval,args.memo_limit)
        if not args.resume:task.install_store(migrate=True)
        original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'storage_conversion' if args.migrate_only else 'running',
            'entrypoint':str(Path(__file__).resolve()),'resume':args.resume})
        if args.migrate_only:
            task.checkpoint('storage_migrated_verified',task.stage)
            original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'storage_migrated_waiting_for_validation'})
            return
        def pause(signum,frame):task.pause_reason=f'Signal {signum}: pause at next safe boundary'
        signal.signal(signal.SIGINT,pause);signal.signal(signal.SIGTERM,pause)
        task.run();original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'construction_complete_validation_pending'})
    except InterruptedError as error:
        original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'paused','reason':str(error)})
    except BaseException as error:
        (out/'error.txt').write_text(traceback.format_exc(),encoding='utf8')
        original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'error','reason':repr(error)})
        raise
    finally:
        if task is not None and hasattr(task,'disk_store'):task.disk_store.close()
        if lock.exists():lock.unlink()


if __name__=='__main__':main()
