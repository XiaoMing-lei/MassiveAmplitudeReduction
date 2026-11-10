"""Small B2 restart records and bounded disposable matching caches.

This wrapper preserves the B2 algebra, its queue, and proof records. It is
tested separately before being used to resume the production extension.
"""
from collections import Counter, defaultdict
import argparse
import gc
import json
from pathlib import Path
import sys
import os
import signal
import subprocess
import traceback
from time import perf_counter

import strategy_bprime as bp
import build_bounded_four_point as b
import construct_parent_descendants as p
from check_b2 import load_b2
from construct_b2 import B2Construction
from extend_b2_resumable import ResumableB2, PauseRequested


class CompactB2(ResumableB2):
    def __init__(self, base, degree, out, checkpoint_interval=900):
        super().__init__(base, degree, out, checkpoint_interval)
        self._last_trim = perf_counter()
        self.report_options['checkpoint_format'] = 'rules_proofs_cursor_v2'
        self.report_options['checkpoint_interval_seconds'] = checkpoint_interval
        self.report_options['disposable_cache_limit_entries'] = 20000
        self.retained_schoutens = {}

    @classmethod
    def resume_compact(cls, folder, out=None):
        tick = perf_counter()
        folder = Path(folder).resolve()
        metadata = json.loads((folder/'restart.json').read_text())
        data = json.loads((folder/'catalog.json').read_text())
        task = cls.__new__(cls)
        B2Construction.__init__(task, metadata['n'], metadata['degree'], out or folder, seconds=0)
        task.engine = load_b2(data)
        for key in ('window', 'phase', 'round_number', 'round_before', 'round_journal_start',
                    'stage', 'rounds', 'report_options'):
            if key in metadata:
                setattr(task, key, metadata[key])
        task.stats = Counter(metadata['stats'])
        task.timings = defaultdict(float, metadata['timings'])
        task.engine.journal = data['journal']
        def pairs(value):
            return value.items() if isinstance(value,dict) else value
        task.engine.epochs = Counter({int(k): v for k,v in pairs(metadata['engine_epochs'])})
        task.engine.version = metadata['engine_version']
        task.engine.stats = Counter(metadata['engine_stats'])
        epochs = {int(k): {int(d):v for d,v in pairs(values)}
                  for k,values in pairs(metadata['parent_epochs'])}
        for saved in data['history_records']:
            rec = task.engine.parents[saved['id']]
            rec['initial_row'] = bp.read_row(saved.get('initial_row', saved['row']))
            rec['updates'] = saved.get('updates', [])
            rec['verified_epochs'] = epochs.get(rec['id'], {})
        task.retained_schoutens = {}
        path = folder/'retained_schouten_descendants.json'
        if path.exists():
            for rec in json.loads(path.read_text()):
                row = bp.read_row(rec['identity'])
                task.retained_schoutens[(rec['source']['parent'],p.encode(row))] = {
                    **rec, 'head': bp.freeze(rec['head']), 'identity': row}
        task.loaded_seconds = metadata['elapsed_seconds']
        task.round_elapsed = metadata['round_elapsed']
        task.checkpoint_interval = 900
        task.pause_requested = task._saving = False
        task._last_control_poll = 0.0
        task.safe_checks = task.pause_after_checks = 0
        task.start = task.round_started = task.last_save = task.last_progress = task._last_trim = perf_counter()
        task.resume_cursor = (task.stage.get('left_parent',0), task.stage.get('right_parent',0))
        task.report_options.update(last_resume_load_seconds=perf_counter()-tick,
            checkpoint_format='rules_proofs_cursor_v2', checkpoint_interval_seconds=900,
            disposable_cache_limit_entries=20000)
        task.engine.budget_check = task.control
        task.reset_overlap_checks()
        return task

    def persistent_descendants(self):
        selected = {}
        for head, items in self.engine.cache.items():
            for row, source in items:
                if source.get('kind') == 'S':
                    key = (source['parent'], p.encode(row))
                    self.retained_schoutens.setdefault(key,
                        {'head':head, 'identity':row, 'source':source})
                block = source.get('block')
                if block is not None and p.degree(block)>p.degree(head):
                    key = (source['parent'],p.encode(row))
                    selected.setdefault(key, {'head':head, 'identity':row, 'source':source})
        return list(selected.values())

    def trim_disposable_caches(self):
        # These are memoized evaluations, not the stored oriented replacements.
        # Keep engine.cache and its exact row order throughout the live run.
        names = ('action_cache', 'original_cache', 'momentum_cache',
                 'momentum_polynomial_cache', 'derived_context_cache', '_block_embeddings')
        for name in names:
            cache = getattr(self.engine, name, None)
            if cache is not None and len(cache)>20000:
                cache.clear()
        # Zero checks can safely be repeated. Do not retain their large proof
        # expressions indefinitely; generated-rule certificates are separate.
        if len(self.host_seen)>20000:
            self.reset_overlap_checks()
        if len(self.exclusions)>20000:
            self.exclusions.clear()
        for module in tuple(sys.modules.values()):
            filename = getattr(module, '__file__', None)
            if not filename or Path(filename).resolve().parent != Path(__file__).resolve().parent:
                continue
            for value in tuple(vars(module).values()):
                if hasattr(value, 'cache_info') and hasattr(value, 'cache_clear'):
                    if value.cache_info().currsize>20000:
                        value.cache_clear()
        gc.collect()
        self._last_trim = perf_counter()

    def control(self):
        # Called only at the same safe boundaries as the old runner.
        if not self._saving and perf_counter()-self._last_trim>30:
            self.trim_disposable_caches()
        return super().control()

    def checkpoint(self, status, stage, full=True):
        if self._saving:
            return
        # The inherited queue requests a save at 120 s; respect the new 900 s
        # policy rather than that old hard-coded request.
        if status=='running' and perf_counter()-self.last_save<self.checkpoint_interval:
            full=False
        self._saving=True
        try:
            self.stage=dict(stage)
            tick=perf_counter()
            active=[r for r in self.engine.parents if r['active']]
            report=dict(particles=self.n,degree=self.degree,status=status,phase=self.phase,
                stage=self.stage,round_number=self.round_number,seconds=self.elapsed(),
                parents=len(active),originals=sum(r['raw'] is not None for r in active),
                parent_degrees=dict(Counter(max(map(p.degree,r['row']),default=2) for r in active)),
                stats=dict(self.stats),reducer_stats=dict(self.engine.stats),timings=dict(self.timings),
                rounds=self.rounds,no_basis_enumeration=True,**self.report_options)
            self.out.mkdir(parents=True,exist_ok=True)
            if full:
                # Write an entire generation in a new directory. Atomically
                # switch the pointer only after all its files are complete.
                generation=self.out/('checkpoint_%012d' % int(self.elapsed()*1000))
                generation.mkdir(exist_ok=False)
                descendants=self.persistent_descendants()
                bp.save(generation/'catalog.json',dict(summary=report,parents=active,
                    history_records=self.engine.parents,journal=self.engine.journal,
                    descendants=descendants))
                bp.save(generation/'retained_schouten_descendants.json',list(self.retained_schoutens.values()))
                self.timings['checkpoint_io_seconds']+=perf_counter()-tick
                tail_tick=perf_counter()
                fields=('n','degree','window','phase','round_number','round_before','round_journal_start',
                        'stage','rounds','stats','timings','report_options')
                metadata={k:getattr(self,k) for k in fields if hasattr(self,k)}
                metadata.update(format=2,elapsed_seconds=self.elapsed(),
                    round_elapsed=self.round_elapsed+perf_counter()-self.round_started,
                    engine_version=self.engine.version,engine_epochs=self.engine.epochs,
                    engine_stats=self.engine.stats,parent_epochs={r['id']:r.get('verified_epochs',{})
                                                                  for r in self.engine.parents})
                bp.save(generation/'restart.json',metadata)
                bp.save(self.out/'latest_checkpoint.json',{'folder':generation.name,
                    'parents':len(active),'stage':self.stage,'phase':self.phase})
                self.timings['checkpoint_io_seconds']+=perf_counter()-tail_tick
                self.last_save=perf_counter()
                if self.phase=='complete':
                    (self.out/'catalog.json').write_bytes((generation/'catalog.json').read_bytes())
                # Keep the current and previous completed checkpoint. Only
                # remove this wrapper's known flat checkpoint directories.
                generations=sorted(self.out.glob('checkpoint_[0-9]*'))
                for old in generations[:-2]:
                    if old.resolve().parent != self.out.resolve():
                        raise RuntimeError('Checkpoint cleanup escaped output directory')
                    allowed={'catalog.json','restart.json','retained_schouten_descendants.json'}
                    files=list(old.iterdir())
                    if any(not f.is_file() or f.name not in allowed for f in files):
                        continue
                    for f in files:f.unlink()
                    old.rmdir()
            report.update(seconds=self.elapsed(),timings=dict(self.timings))
            report['construction_compute_seconds']=report['seconds']-self.timings['checkpoint_io_seconds']
            bp.save(self.out/'progress.json',report)
            self.last_progress=perf_counter()
            print(json.dumps({k:report[k] for k in ('status','phase','stage','seconds','parents')}),flush=True)
            return report
        finally:
            self._saving=False


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--resume',required=True)
    ap.add_argument('--out',required=True)
    ap.add_argument('--verify-on-completion',action='store_true')
    args=ap.parse_args()
    out=Path(args.out).resolve()
    out.mkdir(parents=True,exist_ok=True)
    lock=out/'run.lock'
    with lock.open('x') as stream:stream.write(str(os.getpid()))
    task=None
    try:
        task=CompactB2.resume_compact(args.resume,out)
        if task.phase=='complete':raise RuntimeError('Checkpoint is complete')
        control=out/'control.json'
        if control.exists() and json.loads(control.read_text()).get('action')=='pause':
            raise RuntimeError('Clear the pause request before explicitly resuming')
        if args.verify_on_completion:task.report_options['verify_on_completion']=True
        bp.save(out/'process.json',dict(pid=os.getpid(),status='running',degree=task.degree,
                                       resumed_from=str(Path(args.resume).resolve())))
        hashes=task.source_hashes()
        bp.save(out/'source_hashes.json',hashes)
        snapshot=out/'source_snapshot'
        snapshot.mkdir(exist_ok=True)
        for filename in hashes:
            saved=snapshot/Path(filename).name
            if not saved.exists():saved.write_bytes(Path(filename).read_bytes())
        def request_pause(signum,frame):task.pause_requested=True
        signal.signal(signal.SIGINT,request_pause)
        if hasattr(signal,'SIGTERM'):signal.signal(signal.SIGTERM,request_pause)
        task.run()
        status='completed'
        if task.report_options.get('verify_on_completion'):
            bp.save(out/'process.json',dict(pid=os.getpid(),status='verifying'))
            subprocess.run([sys.executable,'tensor_rules/check_b2.py','--catalog',str(out/'catalog.json')],check=True)
            verified=json.loads((out/'verification.json').read_text())
            status='completed_basic_verification_passed' if not (
                verified['generated_parents_with_reducible_terms'] or verified['old_parent_nonzero_remainders']
                or (verified.get('known_missing_sextic') or {}).get('remainder')) else 'completed_with_verification_failures'
    except PauseRequested:
        task.checkpoint('paused_resumable',task.stage)
        status='paused'
    except BaseException:
        (out/'error.txt').write_text(traceback.format_exc(),encoding='utf-8')
        bp.save(out/'process.json',dict(pid=os.getpid(),status='error',safe_checkpoint_preserved=True))
        raise
    finally:
        lock.unlink(missing_ok=True)
    bp.save(out/'process.json',dict(pid=os.getpid(),status=status))


if __name__=='__main__':main()
