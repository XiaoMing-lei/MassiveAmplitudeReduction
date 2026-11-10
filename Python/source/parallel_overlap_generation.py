"""Pure overlap workers. No catalog mutations, reductions or proof database access."""
from collections import Counter
from pathlib import Path
import os
import pickle
from time import perf_counter, process_time


def initialize(n, degree, stop):
    global c, stopped, memory
    import run_overlap_capped as capped
    import bounded_v32_memoization as memo
    from run_route_pool_overnight import memory
    c, stopped = capped.c, stop
    if n > 4:
        capped.masses.install()
    c.base.old.configure(n, 2*degree)
    memo.bound_function_caches()


def generate(job):
    """Preserve full iterator order and both placements; spool admitted frames."""
    tick, cpu = perf_counter(), process_time()
    counts = Counter()
    chunk = []
    inline, payload_bytes, stream = [], 0, None
    def flush_chunk():
        nonlocal stream, payload_bytes
        if not chunk:
            return
        encoded = pickle.dumps(chunk, protocol=5)
        payload_bytes += len(encoded)
        if stream is None and payload_bytes > 1_000_000:
            stream = Path(job['path']).open('xb')
            pickle.dump(('overlap_frames_v1', job['stamp']), stream, protocol=5)
            for part in inline:
                stream.write(part)
            inline.clear()
        if stream is None:
            inline.append(encoded)
        else:
            stream.write(encoded)
        chunk.clear()
    try:
        for ti, a in job['left_patterns']:
            for tj, z in job['right_patterns']:
                for graph, shared, ap, zp, extra, keys in c.direct.overlap_frames(a, z):
                    if counts['overlap_frames_after_dummy_relabel_dedup'] % 1024 == 0 and stopped.is_set():
                        return {'aborted': True}
                    image = c.b.normalize_graph(*graph)
                    eligible = {head for head in image if c.p.degree(head) <= job['cap']}
                    counts['overlap_frames_after_dummy_relabel_dedup'] += 1
                    counts['normalized_common_terms_above_overlap_cap'] += len(image)-len(eligible)
                    if image and not eligible:
                        counts['overlap_frames_excluded_by_cap'] += 1
                    if eligible:
                        counts['overlap_frames_admitted_by_cap'] += 1
                        chunk.append((ti, tj, a, z, graph, shared, ap, zp, extra, keys, image, eligible))
                        if len(chunk) >= 256:
                            flush_chunk()
        flush_chunk()
    finally:
        if stream is not None:
            stream.close()
    return {'aborted': False, 'counts': dict(counts), 'pid': os.getpid(),
            'worker_seconds': perf_counter()-tick, 'cpu_seconds': process_time()-cpu,
            'bytes': payload_bytes, 'inline': inline if stream is None else None,
            'memory': memory()}


def records(path, stamp, result):
    if result['inline'] is not None:
        for encoded in result['inline']:
            yield from pickle.loads(encoded)
        return
    with Path(path).open('rb') as stream:
        assert pickle.load(stream) == ('overlap_frames_v1', stamp)
        while True:
            try:
                chunk = pickle.load(stream)
            except EOFError:
                return
            yield from chunk
