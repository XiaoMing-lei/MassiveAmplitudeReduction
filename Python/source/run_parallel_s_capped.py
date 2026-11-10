"""Ordered capped construction with speculative parallel S arithmetic."""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, TimeoutError
import heapq
import multiprocessing as mp
from pathlib import Path
import pickle
import sys
import tempfile
from time import perf_counter
import run_parallel_overlap_capped as overlaps
import parallel_s_reduction as workers

serial, original = overlaps.serial, overlaps.original
original.TRANSIENT.add('_s_parallel')


class PendingS:
    def __init__(self, owner):
        tick = perf_counter()
        self.folder = Path(tempfile.mkdtemp(prefix='parallel-s-', dir=owner.out)).resolve()
        self.snapshot = self.folder/'engine.pkl'
        with self.snapshot.open('wb') as stream:
            pickle.dump(workers.engine_snapshot(owner.engine), stream, protocol=5)
        self.version = owner.engine.version
        ctx = mp.get_context('spawn')
        self.stop = ctx.Event()
        self.pool = ProcessPoolExecutor(max_workers=owner.s_worker_count, mp_context=ctx,
                initializer=workers.initialize, initargs=(str(self.snapshot), self.stop))
        self.pending = {}
        self.ticket = 0
        owner.s_parallel_metrics['snapshot_seconds'] += perf_counter()-tick
        owner.s_parallel_metrics['snapshot_bytes_written'] += self.snapshot.stat().st_size
        owner.s_parallel_metrics['pool_generations'] += 1

    def remove(self, key):
        job, future = self.pending.pop(key)
        path = Path(job['path']).resolve()
        assert path.parent == self.folder
        if path.exists():
            path.unlink()

    def close(self):
        self.stop.set()
        self.pool.shutdown(wait=True, cancel_futures=True)
        for key in list(self.pending):
            self.remove(key)
        self.snapshot.unlink()
        self.folder.rmdir()


class ParallelSCappedConstruction(overlaps.ParallelOverlapCappedConstruction):
    s_worker_count = 6
    s_min_degree = 7
    s_min_queue = 24
    entrypoint = str(Path(__file__).resolve())

    def __init__(self, *args, **kwargs):
        self._s_parallel = None
        self.s_parallel_metrics = Counter()
        super().__init__(*args, **kwargs)

    def set_scope(self):
        super().set_scope()
        self.report_options.update(parallel_S_workers=self.s_worker_count,
          parallel_S_min_degree=self.s_min_degree,
          parallel_S_scope='Speculative complete S reductions; every matching choice and negative query validated by the serial live matcher before arithmetic reuse; catalog and proof commits retain original order',
          parallel_S_fallback='Changed choices recomputed with exact replay of the already evaluated matching prefix')

    def report(self, status):
        report = super().report(status)
        report['parallel_S'] = {'workers': self.s_worker_count,
                               'metrics': dict(getattr(self, 's_parallel_metrics', {}))}
        return report

    def close_s(self):
        state = getattr(self, '_s_parallel', None)
        if state is not None:
            state.close()
            self._s_parallel = None

    def run(self):
        if not hasattr(self, 's_parallel_metrics'):
            self.s_parallel_metrics = Counter()
        try:
            return super().run()
        finally:
            self.close_s()

    def process_pair(self, item):
        self.close_s()
        return super().process_pair(item)

    def peek_s(self, limit):
        if not self.s_heap:
            return
        fringe = [(self.s_heap[0], 0)]
        for _ in range(limit):
            if not fringe:
                return
            item, index = heapq.heappop(fringe)
            yield item
            for child in (2*index+1, 2*index+2):
                if child < len(self.s_heap):
                    heapq.heappush(fringe, (self.s_heap[child], child))

    def prefetch_s(self, current):
        tick = perf_counter()
        state = getattr(self, '_s_parallel', None)
        if (state is not None and state.version != self.engine.version
                and current not in state.pending):
            self.close_s()
            state = None
        if state is None:
            self.close_parallel()
            self._s_parallel = state = PendingS(self)
        for item in [current, *self.peek_s(4*self.s_worker_count)]:
            if item in state.pending or item[0] < self.s_min_degree:
                continue
            if item != current and (len(state.pending) >= 3*self.s_worker_count
                                     or state.version != self.engine.version):
                break
            task = self.tasks[item[2]]
            if task['status'] != 'queued' or task['ticket'] != item[1]:
                continue
            state.ticket += 1
            job = {'row': task['current_row'], 'degree': self.degree,
                   'path': str(state.folder/f'{state.ticket:08d}.pkl')}
            state.pending[item] = (job, state.pool.submit(workers.calculate, job))
            self.s_parallel_metrics['tasks_submitted'] += 1
        self.s_parallel_metrics['dispatch_seconds'] += perf_counter()-tick
        return state

    def process_task(self, item):
        if not hasattr(self, 's_parallel_metrics'):
            self.s_parallel_metrics = Counter()
        state = getattr(self, '_s_parallel', None)
        task = self.tasks[item[2]]
        if task['status'] != 'queued' or task['ticket'] != item[1]:
            if state is not None and item in state.pending:
                job, future = state.pending[item]
                if future.done():
                    state.remove(item)
            return super().process_task(item)
        if item[0] < self.s_min_degree or (state is None and len(self.s_heap) < self.s_min_queue):
            return super().process_task(item)
        state = self.prefetch_s(item)
        job, future = state.pending[item]
        tick = perf_counter()
        try:
            while True:
                self.control()
                if self.pause_reason:
                    heapq.heappush(self.s_heap, item)
                    self.boundary()
                try:
                    result = future.result(timeout=0.2)
                    break
                except TimeoutError:
                    pass
        except InterruptedError:
            raise
        except BaseException as error:
            heapq.heappush(self.s_heap, item)
            original.atomic_json(self.out/'parallel_S_worker_error.json', {'ticket': item[1], 'error': repr(error)})
            self.pause_reason = 'Parallel S worker failed; uncommitted task requeued for diagnosis'
            self.boundary()
            raise
        self.s_parallel_metrics['ordered_wait_seconds'] += perf_counter()-tick
        assert not result['aborted']
        data = result['inline'] if result['inline'] is not None else Path(job['path']).read_bytes()
        calls = pickle.loads(data)
        state.remove(item)
        self.s_parallel_metrics['tasks_received'] += 1
        self.s_parallel_metrics['worker_cpu_seconds_sum'] += result['cpu_seconds']
        self.s_parallel_metrics['worker_wall_seconds_sum'] += result['worker_seconds']
        self.s_parallel_metrics['result_bytes'] += result['bytes']
        self.s_parallel_metrics['max_worker_private_bytes'] = max(
            self.s_parallel_metrics['max_worker_private_bytes'], result['memory'].get('process_private_bytes', 0))
        saved_reduce = workers.install_verified_reductions(self.engine, calls, self.s_parallel_metrics)
        try:
            return super().process_task(item)
        finally:
            self.engine.reduce = saved_reduce


if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--s-workers', type=int, default=6)
    parser.add_argument('--s-min-degree', type=int, default=7)
    parser.add_argument('--s-min-queue', type=int, default=24)
    parser.add_argument('--protect-checkpoint', type=int, action='append', default=[])
    args, remaining = parser.parse_known_args()
    assert 1 <= args.workers <= 16 and 1 <= args.s_workers <= 16
    cls = ParallelSCappedConstruction
    cls.worker_count, cls.s_worker_count = args.workers, args.s_workers
    cls.s_min_degree, cls.s_min_queue = args.s_min_degree, args.s_min_queue
    cls.additional_protected_checkpoints = tuple(args.protect_checkpoint)
    sys.argv = [sys.argv[0], *remaining]
    serial.sharing.install()
    serial.timed.base.compact.main(runner_class=cls)
