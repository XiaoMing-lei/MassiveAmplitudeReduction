"""Parallel pure frame generation; unchanged serial, ordered catalog updates.

Only a bounded look-ahead of immutable parent versions is submitted. The
original heaps remain authoritative, and S tasks retain priority. Speculative
spools/futures are disposable: every uncommitted pair stays in the checkpoint
queue, so both serial and parallel runners can restore it.
"""
import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, TimeoutError
import heapq
import multiprocessing as mp
from pathlib import Path
import sys
import tempfile
from time import perf_counter
import run_overlap_capped as serial
import parallel_overlap_generation as workers

c, b, p = serial.c, serial.b, serial.p
original = serial.timed.base.compact.original
original.TRANSIENT.add('_parallel')


class PendingGeneration:
    def __init__(self, owner):
        ctx = mp.get_context('spawn')
        self.stop = ctx.Event()
        self.folder = Path(tempfile.mkdtemp(prefix='parallel-overlaps-', dir=owner.out)).resolve()
        self.pool = ProcessPoolExecutor(max_workers=owner.worker_count, mp_context=ctx,
                                       initializer=workers.initialize,
                                       initargs=(owner.n, owner.degree, self.stop))
        self.pending = {}
        self.ticket = 0

    def remove(self, stamp):
        job, future = self.pending.pop(stamp)
        path = Path(job['path']).resolve()
        assert path.parent == self.folder
        if path.exists():
            path.unlink()

    def close(self):
        self.stop.set()
        self.pool.shutdown(wait=True, cancel_futures=True)
        for stamp in list(self.pending):
            self.remove(stamp)
        self.folder.rmdir()


class ParallelOverlapCappedConstruction(serial.OverlapCappedConstruction):
    worker_count = 4
    parallel_min_degree = 6
    additional_protected_checkpoints = ()
    entrypoint = str(Path(__file__).resolve())

    def __init__(self, *args, **kwargs):
        self._parallel = None
        self.parallel_metrics = Counter()
        super().__init__(*args, **kwargs)

    def set_scope(self):
        super().set_scope()
        self.report_options.update(parallel_overlap_workers=self.worker_count,
            parallel_overlap_min_parent_degree=self.parallel_min_degree,
            parallel_scope='Pure overlap generation, normalization and cap filtering only; ordered serial catalog updates',
            parallel_speculation='Bounded parent-version look-ahead, discarded if stale; original queues authoritative')

    def report(self, status):
        result = super().report(status)
        result['parallel_overlap'] = {'workers': self.worker_count,
                                      'metrics': dict(self.parallel_metrics)}
        return result

    def run(self):
        self.protected_checkpoint_generations = tuple(sorted(set(
            getattr(self, 'protected_checkpoint_generations', (4,))) |
            set(self.additional_protected_checkpoints)))
        try:
            return super().run()
        finally:
            self.close_parallel()

    def close_parallel(self):
        if self._parallel is not None:
            self._parallel.close()
            self._parallel = None

    def peek_pairs(self, limit):
        """Read a sorted heap prefix without popping or scanning the whole heap."""
        if not self.pair_heap:
            return
        fringe = [(self.pair_heap[0], 0)]
        for _ in range(limit):
            if not fringe:
                return
            item, index = heapq.heappop(fringe)
            yield item
            for child in (2*index+1, 2*index+2):
                if child < len(self.pair_heap):
                    heapq.heappush(fringe, (self.pair_heap[child], child))

    def valid_pair(self, item):
        degree, i, j, stamp = item
        return (degree <= self.window and stamp == self.pair_stamp(i, j)
                and all(self.engine.parents[k]['active'] for k in (i, j))
                and stamp not in self.pair_done)

    def prefetch(self, current):
        if self._parallel is None:
            self._parallel = PendingGeneration(self)
        state = self._parallel
        for stamp, (job, future) in list(state.pending.items()):
            if not self.valid_pair(job['item']) and future.done():
                state.remove(stamp)
                self.parallel_metrics['stale_speculative_pairs_discarded'] += 1
        # Always submit the actual next pair, even if obsolete in-flight work
        # briefly occupies all look-ahead slots.
        for item in [current, *self.peek_pairs(4*self.worker_count)]:
            degree, i, j, stamp = item
            if stamp in state.pending or not self.valid_pair(item):
                continue
            if item != current and len(state.pending) >= 2*self.worker_count:
                break
            state.ticket += 1
            job = {'item': item, 'stamp': stamp, 'cap': self.overlap_degree_cap,
                   'left_patterns': list(self.engine.parent_patterns(self.engine.parents[i])),
                   'right_patterns': list(self.engine.parent_patterns(self.engine.parents[j])),
                   'path': str(state.folder/f'{state.ticket:08d}.pkl')}
            state.pending[stamp] = (job, state.pool.submit(workers.generate, job))
            self.parallel_metrics['pairs_submitted'] += 1

    def process_capped_pair(self, item):
        if item[0] < self.parallel_min_degree:
            return super().process_capped_pair(item)
        degree, i, j, stamp = item
        self.pair_scheduled.discard(stamp)
        if stamp != self.pair_stamp(i, j) or not all(self.engine.parents[k]['active'] for k in (i, j)):
            self.stats['obsolete_pair_versions_skipped'] += 1
            return
        if stamp in self.pair_done:
            return
        tick = perf_counter()
        self.prefetch(item)
        self.parallel_metrics['dispatch_seconds'] += perf_counter()-tick
        job, future = self._parallel.pending[stamp]
        tick = perf_counter()
        while True:
            self.control()
            if self.pause_reason:
                # Nothing from this pair has been committed; put it back before
                # the usual atomic checkpoint and safe exit.
                heapq.heappush(self.pair_heap, item)
                self.pair_scheduled.add(stamp)
                self.boundary()
            try:
                result = future.result(timeout=0.2)
                break
            except TimeoutError:
                continue
            except BaseException as error:
                heapq.heappush(self.pair_heap, item)
                self.pair_scheduled.add(stamp)
                original.atomic_json(self.out/'parallel_worker_error.json', {'pair': item, 'error': repr(error)})
                self.pause_reason = 'Parallel worker failed; uncommitted pair requeued for diagnosis'
                self.boundary()
                raise
        self.parallel_metrics['ordered_wait_seconds'] += perf_counter()-tick
        assert not result['aborted']
        assert stamp == self.pair_stamp(i, j)
        self.current_pair = item
        self.stage = {'parent_degree': self.window, 'left_parent': i, 'right_parent': j,
                      'phase': 'direct_parent_overlaps'}
        self.stats['parent_pairs'] += 1
        self.stats.update(result['counts'])
        self.parallel_metrics['pairs_committed'] += 1
        self.parallel_metrics['committed_worker_cpu_seconds'] += result['cpu_seconds']
        self.parallel_metrics['committed_worker_wall_seconds_sum'] += result['worker_seconds']
        self.parallel_metrics['committed_spool_bytes'] += result['bytes']
        self.parallel_metrics['max_sampled_worker_private_bytes'] = max(
            self.parallel_metrics['max_sampled_worker_private_bytes'], result['memory']['process_private_bytes'])
        # Worker CPU totals overlap in time; do not add them to serial wall timers.
        tick = perf_counter()
        for ti, tj, a, z, graph, shared, ap, zp, extra, keys, image, eligible in workers.records(job['path'], stamp, result):
            self.parallel_metrics['ordered_read_seconds'] += perf_counter()-tick
            self.control()
            origin = {'parents': [i, j], 'parent_versions': [stamp[1], stamp[3]],
                      'terms': [ti, tj], 'shared_brackets': shared,
                      'common_graph': graph, 'additional_contractions': extra}
            rows = [self.direct_route(i, ti, a, graph, ap, keys[0]),
                    self.direct_route(j, tj, z, graph, zp, keys[1])]
            actual = []
            for row, source in rows:
                head = max(row, key=b.mkey, default=None)
                if head not in image:
                    self.stats['proposed_occurrence_not_actual_LM'] += 1
                    actual.append(None)
                    continue
                if head not in eligible:
                    self.stats['actual_contextual_heads_excluded_by_cap'] += 1
                    actual.append(None)
                    continue
                actual.append(self.register_route(head, row, source, origin))
            if all(r is not None for r in actual) and self.routes[actual[0]]['head'] == self.routes[actual[1]]['head']:
                self.stats['two_actual_LMs_in_supplied_pair'] += 1
            tick = perf_counter()
        self.parallel_metrics['ordered_read_seconds'] += perf_counter()-tick
        self.pair_done.add(stamp)
        self.current_pair = None
        self._parallel.remove(stamp)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--parallel-min-degree', type=int, default=6)
    parser.add_argument('--protect-checkpoint', type=int, action='append', default=[])
    args, remaining = parser.parse_known_args()
    assert 1 <= args.workers <= 16
    ParallelOverlapCappedConstruction.worker_count = args.workers
    ParallelOverlapCappedConstruction.parallel_min_degree = args.parallel_min_degree
    ParallelOverlapCappedConstruction.additional_protected_checkpoints = tuple(args.protect_checkpoint)
    sys.argv = [sys.argv[0], *remaining]
    serial.sharing.install()
    serial.timed.base.compact.main(runner_class=ParallelOverlapCappedConstruction)
