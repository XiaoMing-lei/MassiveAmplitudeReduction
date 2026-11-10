"""Disk route runner with losslessly compressed polynomial identifiers.

No order/cutoff/matching changes. Heap priorities stay (degree,ticket), and
the core S-task routine receives the original decoded polynomial encoding.
"""
import argparse,gc,json,os,signal,traceback
from pathlib import Path
from time import perf_counter
import run_disk_route_pool as disk_run
import durable_route_storage as storage
import compressed_polynomial_keys as keys
import bounded_v32_memoization as bounded_v32

original=disk_run.original
original.bound_function_caches=bounded_v32.bound_function_caches
old_key_bytes=storage.key_bytes


def exact_key_bytes(value):
    return value.data if isinstance(value,keys.Key) else old_key_bytes(value)


storage.key_bytes=exact_key_bytes


class CompactTaskMap(storage.DiskMap):
    def __contains__(self,key):return super().__contains__(keys.pack(key))
    def __getitem__(self,key):return super().__getitem__(keys.pack(key))
    def __setitem__(self,key,value):return super().__setitem__(keys.pack(key),value)
    def __delitem__(self,key):return super().__delitem__(keys.pack(key))


class CompactOvernight(disk_run.DiskOvernight):
    def compact_indices(self):
        tick=perf_counter();changed=False
        for name in ('known_cache_polynomials',):
            if not isinstance(getattr(self,name),keys.EncodedSet):
                setattr(self,name,keys.EncodedSet(getattr(self,name)));changed=True
        for owner,name in ((self,'checks_by_parent'),(self,'blocked'),(self.engine,'cache_encodings')):
            current=getattr(owner,name)
            if not isinstance(current,keys.EncodingIndex):
                setattr(owner,name,keys.EncodingIndex(current));changed=True
        if changed:self.timings['identifier_compaction_seconds']+=perf_counter()-tick

    def bound_memos(self):
        super().bound_memos()
        if hasattr(self,'known_cache_polynomials'):self.compact_indices()

    def install_store(self,migrate=False):
        super().install_store(migrate)
        self.tasks.__class__=CompactTaskMap
        tick=perf_counter()
        self.s_heap=[(degree,ticket,keys.pack(key)) for degree,ticket,key in self.s_heap]
        self.timings['identifier_compaction_seconds']+=perf_counter()-tick
        self.compact_indices()
        self.report_options.update(queue_identifier_storage='Lossless compressed polynomial keys; original hash retained',
            queue_priority_unchanged='degree, then unique insertion ticket',state_key_format_version=1,
            function_cache_scope='All v3.2 source modules and arithmetic aliases')

    def enqueue_task(self,key,task):
        return super().enqueue_task(keys.pack(key),task)

    def process_task(self,item):
        degree,ticket,key=item
        return super().process_task((degree,ticket,keys.unpack(key)))

    def report(self,status):
        report=super().report(status)
        report['identifier_compaction_seconds']=self.timings['identifier_compaction_seconds']
        maintenance=self.timings['identifier_conversion_maintenance_seconds']
        report['storage_maintenance_seconds']+=maintenance
        report['cumulative_construction_seconds']-=maintenance
        report['construction_compute_seconds']-=maintenance
        report['pure_function_caches']=bounded_v32.cache_inventory()
        return report


def main(runner_class=CompactOvernight):
    parser=argparse.ArgumentParser();parser.add_argument('--out',required=True)
    parser.add_argument('--particles',type=int,default=4);parser.add_argument('--degree',type=int,default=8)
    parser.add_argument('--resume',action='store_true');parser.add_argument('--migrate-only',action='store_true')
    parser.add_argument('--memo-limit',type=int,default=20000)
    args=parser.parse_args();out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=args.resume)
    control=out/'control.json'
    if control.exists() and json.loads(control.read_text()).get('action')=='pause':raise RuntimeError('A pause is pending')
    lock=out/'run.lock'
    with lock.open('x') as stream:stream.write(str(os.getpid()))
    task=None
    try:
        previous_compaction=(json.loads((out/'latest_checkpoint.json').read_text())['timings'].get(
            'identifier_compaction_seconds',0) if args.resume else 0)
        task=runner_class.restore(out) if args.resume else runner_class(args.particles,args.degree,out,memo_limit=args.memo_limit)
        if not args.resume:task.install_store(migrate=True)
        task.protected_checkpoint_generations=(4,)
        original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'identifier_conversion' if args.migrate_only else 'running',
            'entrypoint':getattr(runner_class,'entrypoint',str(Path(__file__).resolve())),'resume':args.resume})
        if args.migrate_only:
            task.timings['identifier_conversion_maintenance_seconds']+=max(
                0,task.timings['identifier_compaction_seconds']-previous_compaction)
            task.checkpoint('storage_migrated_verified',task.stage)
            original.atomic_json(out/'process.json',{'pid':os.getpid(),'status':'identifier_conversion_waiting_for_validation'})
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
