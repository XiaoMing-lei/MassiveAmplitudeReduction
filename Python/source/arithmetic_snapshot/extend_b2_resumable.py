"""Resumable B2 extension, with unchanged algebra and no amplitude basis.

The restart file is a trusted local pickle, replaced atomically. Checkpoints
are taken between completed overlap cancellations or interreduction steps.
Resume repeats the interrupted parent pair, retaining its verified checks.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path
import pickle
import signal
import subprocess
import sys
from time import perf_counter
import traceback

import strategy_bprime as bp
import construct_parent_descendants as p
from construct_b2 import B2Construction
from check_b2 import load_b2


class PauseRequested(Exception):
    pass


class ResumableB2(B2Construction):
    def __init__(self, base, degree, out, checkpoint_interval=120):
        tick=perf_counter()
        path=Path(base).resolve()
        data=json.loads(path.read_text())
        summary=data['summary']
        assert summary['status']=='completed_bounded_interreduced_queue'
        assert summary.get('strategy')=='B2'
        assert summary['degree']<degree
        super().__init__(summary['particles'],degree,out,seconds=0)
        self.engine=load_b2(data)
        self.engine.degree=degree
        self.engine.journal=list(data['journal'])
        self.engine.epochs=Counter({d:1 for d in range(2,summary['degree']+1)})
        for saved in data['history_records']:
            rec=self.engine.parents[saved['id']]
            rec['initial_row']=bp.read_row(saved.get('initial_row',saved['row']))
            rec['updates']=list(saved.get('updates',[]))
            rec['verified_epochs']=dict(self.engine.epochs)
        # A completed lower window is reused, but all new-window parent pairs
        # are examined. Do not infer stability of zero reductions under an
        # additional contraction or reuse old omission certificates blindly.
        self.engine.version=len(self.engine.parents)+len(self.engine.journal)
        self.window=summary['degree']+1
        self.phase='new_window'
        self.round_number=0
        self.round_before=len(self.engine.parents)
        self.round_elapsed=0.0
        self.round_started=perf_counter()
        self.resume_cursor=(0,0)
        self.checkpoint_interval=checkpoint_interval
        self.pause_requested=False
        self._saving=False
        self._last_control_poll=0.0
        self.safe_checks=0
        self.pause_after_checks=0  # test-only injection; never enabled by CLI
        self.loaded_seconds=0.0
        self.start=perf_counter()
        self.last_save=self.last_progress=self.start
        self.stage={'window':self.window,'left_parent':0,'right_parent':0}
        self.report_options.update(base_catalog=str(path),base_degree=summary['degree'],
            base_parent_count=len(data['parents']),base_construction_seconds=summary['seconds'],
            checkpoint_load_seconds=self.start-tick,timing_scope='extension only; degree-six result reused',
            no_time_limit=True,no_component_construction=True,
            resumable_checkpoint=True,checkpoint_interval_seconds=checkpoint_interval)
        self.engine.budget_check=self.control

    @classmethod
    def resume(cls,path):
        tick=perf_counter()
        path=Path(path).resolve()
        with gzip.open(path,'rb') as stream:state=pickle.load(stream)
        if state['format']!=1:raise ValueError('Unsupported checkpoint format')
        # Verify code before restoring objects; only locally created trusted
        # restart files may be used by this runner.
        for filename,expected in state['source_hashes'].items():
            actual=hashlib.sha256(Path(filename).read_bytes()).hexdigest()
            if actual!=expected:raise RuntimeError('Source changed since checkpoint: '+filename)
        task=cls.__new__(cls)
        task.__dict__.update(state['task'])
        bp.configure(task.n,task.degree)
        task.loaded_seconds=state['elapsed_seconds']
        task.round_elapsed=state['round_elapsed']
        task.start=task.round_started=perf_counter()
        task.last_save=task.last_progress=task.start
        task._last_control_poll=0.0
        task._saving=False
        task.pause_requested=False
        task.pause_after_checks=0
        task.report_options['last_resume_load_seconds']=perf_counter()-tick
        task.engine.budget_check=task.control
        if task.phase=='overlaps':
            task.resume_cursor=(task.stage.get('left_parent',0),task.stage.get('right_parent',0))
        return task

    def elapsed(self):return self.loaded_seconds+perf_counter()-self.start

    @staticmethod
    def source_hashes():
        folder=Path(__file__).resolve().parent
        # All Python implementation files imported from the tensor_rules
        # directory. Ignore unrelated report scripts not loaded by this run.
        files={Path(__file__).resolve()}
        for module in tuple(sys.modules.values()):
            filename=getattr(module,'__file__',None)
            if filename:
                path=Path(filename).resolve()
                if path.parent==folder and path.suffix=='.py':files.add(path)
        return {str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(files)}

    def control(self):
        if self._saving:return
        now=perf_counter()
        if now-self._last_control_poll>=1:
            self._last_control_poll=now
            request=self.out/'control.json'
            if request.exists():
                try:self.pause_requested |= json.loads(request.read_text()).get('action')=='pause'
                except (OSError,json.JSONDecodeError):pass
        if self.pause_requested:raise PauseRequested('Pause requested; saving restart state.')
        if now-self.last_save>=self.checkpoint_interval:
            self.checkpoint('running',self.stage,full=True)
        elif now-self.last_progress>=30:
            self.checkpoint('running',self.stage,full=False)

    def check_host(self,mon,origin):
        result=super().check_host(mon,origin)
        self.safe_checks+=1
        if self.pause_after_checks and self.safe_checks>=self.pause_after_checks:
            self.pause_requested=True
        self.control()
        return result

    def contextual_overlap(self,mon,origin,pair,seen):
        self.control()
        return super().contextual_overlap(mon,origin,pair,seen)

    def checkpoint(self,status,stage,full=True):
        if self._saving:return
        self._saving=True
        try:
            self.stage=dict(stage)
            tick=perf_counter()
            active=[r for r in self.engine.parents if r['active']]
            report=dict(particles=self.n,degree=self.degree,status=status,phase=self.phase,
                stage=self.stage,round_number=self.round_number,seconds=self.elapsed(),
                parents=len(active),originals=sum(r['raw'] is not None for r in active),
                parent_degrees=dict(Counter(max(map(p.degree,r['row']),default=2) for r in active)),
                historical_parent_records=len(self.engine.parents),stats=dict(self.stats),
                reducer_stats=dict(self.engine.stats),timings=dict(self.timings),rounds=self.rounds,
                no_basis_enumeration=True,**self.report_options)
            self.out.mkdir(parents=True,exist_ok=True)
            if full:
                target=self.out/'resume_state.pkl.gz'
                temporary=self.out/'resume_state.pkl.gz.tmp'
                callback=self.engine.budget_check
                del self.engine.budget_check
                try:
                    state=dict(format=1,task=dict(self.__dict__),elapsed_seconds=self.elapsed(),
                        round_elapsed=self.round_elapsed+perf_counter()-self.round_started,
                        source_hashes=self.source_hashes())
                    with gzip.open(temporary,'wb',compresslevel=1) as stream:
                        pickle.dump(state,stream,protocol=5)
                    os.replace(temporary,target)
                finally:self.engine.budget_check=callback
                bp.save(self.out/'catalog.json',dict(summary=report,parents=active,
                    history_records=self.engine.parents,journal=self.engine.journal,
                    full_search_archive='resume_state.pkl.gz'))
                bp.save(self.out/'checkpoint_info.json',dict(status=status,phase=self.phase,
                    stage=self.stage,parents=len(active),elapsed_seconds=self.elapsed(),
                    restart_file='resume_state.pkl.gz',restart_bytes=target.stat().st_size,
                    resume_repeats_current_parent_pair=True))
                self.timings['checkpoint_io_seconds']+=perf_counter()-tick
                self.last_save=perf_counter()
            report.update(seconds=self.elapsed(),timings=dict(self.timings))
            report['construction_compute_seconds']=report['seconds']-self.timings['checkpoint_io_seconds']
            bp.save(self.out/'progress.json',report)
            self.last_progress=perf_counter()
            print(json.dumps({k:report[k] for k in
                ('status','phase','stage','seconds','parents','parent_degrees')}),flush=True)
            return report
        finally:self._saving=False

    def run(self):
        self.checkpoint('extension_started' if self.phase=='new_window' else 'resumed',self.stage)
        while self.window<=self.degree:
            self.control()
            if self.phase=='new_window':
                self.round_number=0
                self.phase='new_round'
            if self.phase=='new_round':
                self.round_number+=1
                self.round_before=len(self.engine.parents)
                self.round_journal_start=len(self.engine.journal)
                self.round_elapsed=0.0
                self.round_started=perf_counter()
                self.reset_overlap_checks()
                self.resume_cursor=(0,0)
                self.stage={'window':self.window,'left_parent':0,'right_parent':0}
                self.phase='overlaps'
                self.checkpoint('round_started',self.stage)
            if self.phase=='overlaps':
                self.run_window(*self.resume_cursor)
                self.phase='interreduce'
                self.checkpoint('overlap_queue_finished',self.stage)
            if self.phase=='interreduce':
                tick=perf_counter()
                changed=self.engine.interreduce()
                self.timings['backward_reduction_seconds']+=perf_counter()-tick
                self.rounds.append(dict(window=self.window,round=self.round_number,
                    insertions=len(self.engine.parents)-self.round_before,presentation_updates=changed,
                    active_parents=sum(r['active'] for r in self.engine.parents),
                    seconds=self.round_elapsed+perf_counter()-self.round_started))
                # Epochs survive a pause during interreduction. Even when this
                # invocation returns zero, updates before that pause require
                # another overlap round. Compare the saved journal length.
                changed_since_round=any(event['event']=='update' for event in
                    self.engine.journal[self.round_journal_start:]) if hasattr(self,'round_journal_start') else bool(changed)
                self.phase='new_round' if changed_since_round else 'window_finished'
                self.checkpoint('backward_pass_finished',{'window':self.window,'round':self.round_number})
                if self.phase=='new_round':continue
            if self.phase=='window_finished':
                self.checkpoint('window_completed',{'window':self.window,'rounds':self.round_number})
                self.window+=1
                self.phase='new_window'
                self.stage={'window':self.window,'left_parent':0,'right_parent':0}
        self.phase='complete'
        self.stage={'window':self.degree}
        return self.checkpoint('completed_bounded_interreduced_queue',self.stage)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--base')
    ap.add_argument('--degree',type=int,default=8)
    ap.add_argument('--out')
    ap.add_argument('--resume')
    ap.add_argument('--checkpoint-interval',type=float,default=120)
    ap.add_argument('--verify-on-completion',action='store_true')
    args=ap.parse_args()
    if args.resume:
        task=ResumableB2.resume(args.resume)
        if task.phase=='complete':raise SystemExit('Checkpoint is already complete.')
        control=task.out/'control.json'
        if control.exists() and json.loads(control.read_text()).get('action')=='pause':
            raise SystemExit('Clear the saved pause request before explicitly resuming.')
    else:
        if not args.base or not args.out:ap.error('--base and --out are required for an extension')
        if (Path(args.out)/'resume_state.pkl.gz').exists():
            raise SystemExit('Existing restart file: use --resume rather than overwrite it.')
        task=ResumableB2(args.base,args.degree,args.out,args.checkpoint_interval)
    if args.verify_on_completion:task.report_options['verify_on_completion']=True
    lock=task.out/'run.lock'
    task.out.mkdir(parents=True,exist_ok=True)
    try:
        with lock.open('x') as stream:stream.write(str(os.getpid()))
    except FileExistsError:
        raise SystemExit('Run lock exists. Check its PID before removing a stale lock.')
    bp.save(task.out/'process.json',dict(pid=os.getpid(),status='running',base=args.base,degree=task.degree))
    hashes=task.source_hashes()
    bp.save(task.out/'source_hashes.json',hashes)
    snapshot=task.out/'source_snapshot'
    snapshot.mkdir(exist_ok=True)
    for filename in hashes:
        saved=snapshot/Path(filename).name
        if not saved.exists():saved.write_bytes(Path(filename).read_bytes())
    def request_pause(signum,frame):task.pause_requested=True
    signal.signal(signal.SIGINT,request_pause)
    if hasattr(signal,'SIGTERM'):signal.signal(signal.SIGTERM,request_pause)
    try:
        task.run()
        status='completed'
        if task.report_options.get('verify_on_completion'):
            bp.save(task.out/'process.json',dict(pid=os.getpid(),status='verifying'))
            subprocess.run([sys.executable,'tensor_rules/check_b2.py','--catalog',str(task.out/'catalog.json')],check=True)
            verified=json.loads((task.out/'verification.json').read_text())
            if (verified['generated_parents_with_reducible_terms'] or verified['old_parent_nonzero_remainders']
                    or (verified.get('known_missing_sextic') or {}).get('remainder')):
                status='completed_with_verification_failures'
            else:status='completed_basic_verification_passed'
    except PauseRequested:
        task.checkpoint('paused_resumable',task.stage)
        status='paused'
    except BaseException:
        # Unexpected interruption could occur inside an incomplete action.
        # Keep the last safe restart file; do not replace it with partial state.
        (task.out/'error.txt').write_text(traceback.format_exc(),encoding='utf-8')
        bp.save(task.out/'process.json',dict(pid=os.getpid(),status='error',safe_checkpoint_preserved=True))
        raise
    finally:
        lock.unlink(missing_ok=True)
    bp.save(task.out/'process.json',dict(pid=os.getpid(),status=status))


if __name__=='__main__':main()
