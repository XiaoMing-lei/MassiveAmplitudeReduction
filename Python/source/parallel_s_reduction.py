"""Speculative S reductions with ordered, live-matcher transcript validation.

Workers never write the parent catalog or proof database. Before using a
worker reduction the coordinator makes the very same matching queries in
order, including unsuccessful queries. Thus cache discoveries are made by
the authoritative matcher, and an outdated choice causes an exact serial
continuation. Parent insertion/interreduction and task commits stay serial.
"""
from collections import Counter
import gc
import os
from pathlib import Path
import pickle
from time import perf_counter, process_time


def engine_snapshot(engine):
    import run_route_pool_overnight as runtime
    omitted = runtime.DISPOSABLE | {'parents', 'journal', 'stats',
                                   '_prepared_parent_terms'}
    state = {k: v for k, v in vars(engine).items()
             if k not in omitted and not callable(v)}
    state['parents'] = [{k: rec[k] for k in ('id', 'family', 'labels', 'raw',
                         'row', 'active', 'revision') if k in rec}
                        for rec in engine.parents]
    state['journal'] = []
    state['stats'] = Counter()
    # Preserve the actual matching choices already memoized at the snapshot.
    # Other disposable caches only avoid recomputing pure matching data.
    state['action_cache'] = dict(engine.action_cache)
    return state


def initialize(path, stop):
    global engine, stopped, c, memory, initial_seconds
    tick = perf_counter()
    import run_overlap_capped as capped
    import bounded_v32_memoization as bounded
    from run_route_pool_overnight import memory, Memo, CACHE_LIMITS
    c, stopped = capped.c, stop
    enabled = gc.isenabled()
    gc.disable()
    try:
        with open(path, 'rb') as stream:
            state = pickle.load(stream)
    finally:
        if enabled:
            gc.enable()
    if state['n'] > 4:
        capped.masses.install()
    c.base.old.configure(state['n'], 2*state['degree'])
    bounded.bound_function_caches()
    engine = c.old.QueueReducer.__new__(c.old.QueueReducer)
    vars(engine).update(state)
    for name, limit in CACHE_LIMITS.items():
        setattr(engine, name, Memo(min(limit, 20000), getattr(engine, name, {})))
    engine._prepared_parent_terms = {}
    def control():
        if stopped.is_set():
            raise InterruptedError('Speculative S work cancelled')
    engine.budget_check = control
    initial_seconds = perf_counter()-tick


def calculate(job):
    """Return each external reduce() call and its complete action transcript."""
    tick, cpu = perf_counter(), process_time()
    original_reduce, original_actions = engine.reduce, engine.actions
    calls, active = [], []
    def actions(mon, first_only=False):
        answer = original_actions(mon, first_only=first_only)
        if active:
            active[-1].append((mon, first_only, answer))
        return answer
    def reduce(row, *args, **kwargs):
        # Nested momentum-only preparation is repeated inside the live matcher
        # during coordinator validation; it is not a speculative outer call.
        if args or kwargs.get('only_m', False):
            return original_reduce(row, *args, **kwargs)
        record = {'input': row, 'kwargs': kwargs, 'actions': []}
        active.append(record['actions'])
        try:
            result = original_reduce(row, **kwargs)
            record.update(result=result, blocked=False)
            return result
        except c.base.AboveDegreeRemainder as stop:
            record.update(blocked=True, head=stop.head, bound=stop.bound,
                          partial_row=stop.partial_row, denominator=stop.denominator,
                          reduction_steps=stop.reduction_steps, count=stop.steps)
            raise
        finally:
            active.pop()
            calls.append(record)
    engine.actions, engine.reduce = actions, reduce
    try:
        try:
            result, den, steps = engine.reduce(job['row'], trace=True,
                                               degree_bound=job['degree'])
            row, factor, scale = c.p.primitive(result)
            while row and engine.candidate_term_actions(row):
                result, d2, more = engine.reduce(result, trace=True)
                if not more:
                    raise RuntimeError('Primitive-only match requires explicit replay')
                row, factor, scale = c.p.primitive(result)
        except c.base.AboveDegreeRemainder:
            pass
        data = pickle.dumps(calls, protocol=5)
        inline = data if len(data) <= 1_000_000 else None
        if inline is None:
            Path(job['path']).write_bytes(data)
        return {'aborted': False, 'inline': inline, 'bytes': len(data),
                'worker_seconds': perf_counter()-tick, 'cpu_seconds': process_time()-cpu,
                'memory': memory(), 'pid': os.getpid(), 'initial_seconds': initial_seconds}
    except InterruptedError:
        return {'aborted': True}
    finally:
        engine.reduce, engine.actions = original_reduce, original_actions


def install_verified_reductions(engine, calls, metrics):
    """Temporarily substitute verified results into the unchanged task routine.

On a changed action, replay the already evaluated matching-query prefix while
the ordinary reducer rebuilds its arithmetic state. This avoids both extra
cache discoveries and changing earlier choices because of a later query.
"""
    from construct_degree_queue import base, b
    original_reduce = engine.reduce
    cursor = 0
    def reduce(row, *args, **kwargs):
        nonlocal cursor
        if args or kwargs.get('only_m', False) or cursor >= len(calls):
            return original_reduce(row, *args, **kwargs)
        record = calls[cursor]
        cursor += 1
        if row != record['input'] or kwargs != record['kwargs']:
            cursor = len(calls)
            metrics['input_changed_serial_fallbacks'] += 1
            return original_reduce(row, **kwargs)
        original_actions = engine.actions
        prefix = []
        tick = perf_counter()
        for mon, first_only, expected in record['actions']:
            actual = original_actions(mon, first_only=first_only)
            prefix.append((mon, first_only, actual))
            if actual != expected:
                metrics['changed_action_serial_fallbacks'] += 1
                cursor = len(calls)
                position = 0
                def replay_actions(m, first_only=False):
                    nonlocal position
                    if position < len(prefix):
                        prior_mon, prior_flag, answer = prefix[position]
                        assert (m, first_only) == (prior_mon, prior_flag), 'Reduction transcript prefix diverged'
                        position += 1
                        return answer
                    return original_actions(m, first_only=first_only)
                engine.actions = replay_actions
                try:
                    return original_reduce(row, **kwargs)
                finally:
                    engine.actions = original_actions
                    metrics['live_match_validation_seconds'] += perf_counter()-tick
        metrics['live_match_validation_seconds'] += perf_counter()-tick
        metrics['verified_reduce_calls'] += 1
        if record['blocked']:
            engine.stats['early_above_degree_stops'] += 1
            stop = base.AboveDegreeRemainder(record['head'], record['bound'], None, record['count'])
            stop.partial_row = record['partial_row']
            stop.denominator = record['denominator']
            stop.reduction_steps = record['reduction_steps']
            raise stop
        result = record['result']
        engine.stats['reduction_steps'] += len(result[2])
        metrics['verified_arithmetic_steps'] += len(result[2])
        return result
    engine.reduce = reduce
    return original_reduce
