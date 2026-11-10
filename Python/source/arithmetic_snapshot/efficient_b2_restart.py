"""B2 continuation with bounded LRU memoization and durable exact zero checks.

Only storage and reuse change. Algebra, contextual LM tests, overlap generation,
and backward reduction are inherited unchanged from the verified B2 code.
"""
from collections import OrderedDict, deque
from functools import lru_cache
from pathlib import Path
import sqlite3
import sys
from time import perf_counter
import zlib

import compact_b2_restart as compact
from construct_b2 import B2Reducer
from extend_b2_resumable import ResumableB2


class BoundedCache(dict):
    """Dictionary with incremental least-recently-used eviction."""
    def __init__(self, capacity, initial=()):
        super().__init__()
        self.capacity=capacity
        self.recency=OrderedDict()
        self.evictions=0
        self.update(initial)

    def __getitem__(self,key):
        value=super().__getitem__(key)
        self.recency.move_to_end(key)
        return value

    def get(self,key,default=None):
        try:return self[key]
        except KeyError:return default

    def __setitem__(self,key,value):
        super().__setitem__(key,value)
        self.recency[key]=None
        self.recency.move_to_end(key)
        while len(self)>self.capacity:
            oldest,_=self.recency.popitem(last=False)
            super().__delitem__(oldest)
            self.evictions+=1

    def update(self,values=(),**kwargs):
        for key,value in (values.items() if hasattr(values,'items') else values):
            self[key]=value
        for key,value in kwargs.items():self[key]=value

    def clear(self):
        super().clear()
        self.recency.clear()

    def __delitem__(self,key):
        super().__delitem__(key)
        del self.recency[key]


CACHE_LIMITS={
    'action_cache':50000, 'original_cache':20000, 'momentum_cache':50000,
    'momentum_polynomial_cache':20000, 'derived_context_cache':50000,
    '_block_embeddings':20000,
}


def install_engine_caches(engine):
    for name,limit in CACHE_LIMITS.items():
        current=getattr(engine,name,{})
        if not isinstance(current,BoundedCache):
            setattr(engine,name,BoundedCache(limit,current))


class EfficientReducer(B2Reducer):
    def add_parent(self,row,source):
        result=super().add_parent(row,source)
        install_engine_caches(self)
        return result

    def replace_parent(self,pid,row,proof):
        result=super().replace_parent(pid,row,proof)
        install_engine_caches(self)
        return result


def bound_function_caches():
    """Replace unbounded pure-function memoizers, preserving shared aliases."""
    folder=Path(__file__).resolve().parent
    replacements={}
    changed=[]
    for module in tuple(sys.modules.values()):
        filename=getattr(module,'__file__',None)
        if not filename or Path(filename).resolve().parent!=folder:continue
        for name,value in tuple(vars(module).items()):
            if not hasattr(value,'cache_info') or not hasattr(value,'__wrapped__'):continue
            if value.cache_info().maxsize is not None:continue
            identity=id(value)
            if identity not in replacements:
                limit=2000 if value.__name__=='external_children' else 50000
                replacements[identity]=lru_cache(maxsize=limit)(value.__wrapped__)
            setattr(module,name,replacements[identity])
            changed.append(module.__name__+'.'+name)
    return changed


class CompletedChecks:
    """Exact compressed polynomial encodings, not probabilistic hash keys.

    Version tags exclude checks relying on rules absent from a restored
    checkpoint. A new degree/overlap round invalidates previous checks just as
    the original constructor did. Normal cache maintenance never deletes them.
    """
    def __init__(self,path,version):
        self.path=Path(path)
        self.path.parent.mkdir(parents=True,exist_ok=True)
        self.version=version
        self.scope=None
        self.hot=BoundedCache(20000)
        self.connection=sqlite3.connect(self.path)
        self.connection.execute('PRAGMA journal_mode=WAL')
        self.connection.execute('PRAGMA synchronous=NORMAL')
        self.connection.execute('PRAGMA cache_size=-8192')
        self.connection.execute('CREATE TABLE IF NOT EXISTS checks '
            '(scope TEXT NOT NULL, polynomial BLOB NOT NULL, version INTEGER NOT NULL, '
            'PRIMARY KEY(scope,polynomial)) WITHOUT ROWID')
        self.hits=self.misses=self.additions=0

    def begin_scope(self,scope,resuming=False):
        if scope!=self.scope:
            self.connection.execute('DELETE FROM checks WHERE scope<>?',(scope,))
            self.scope=scope
            self.hot.clear()
        if resuming:
            # Discard durable checks created after the rule checkpoint. Their
            # numeric version must not be reused for a different continuation.
            self.connection.execute('DELETE FROM checks WHERE version>?',(self.version(),))
            self.hot.clear()
        self.connection.commit()

    @staticmethod
    def key(value):
        # Polynomial encodings consist of canonical nested tuples of integers.
        # Their repr is exact; lossless compression introduces no hash collision.
        return zlib.compress(repr(value).encode('ascii'),1)

    def __contains__(self,value):
        key=self.key(value)
        version=self.hot.get(key)
        if version is None:
            found=self.connection.execute('SELECT version FROM checks WHERE scope=? AND polynomial=?',
                                          (self.scope,key)).fetchone()
            if found is not None:
                version=found[0]
                self.hot[key]=version
        if version is not None and version<=self.version():
            self.hits+=1
            return True
        self.misses+=1
        return False

    def add(self,value):
        key=self.key(value)
        version=self.version()
        self.connection.execute('INSERT INTO checks VALUES (?,?,?) ON CONFLICT(scope,polynomial) '
            'DO UPDATE SET version=min(version,excluded.version)',(self.scope,key,version))
        self.hot[key]=min(version,self.hot.get(key,version))
        self.additions+=1

    def __len__(self):
        return self.connection.execute('SELECT count(*) FROM checks WHERE scope=?',(self.scope,)).fetchone()[0]

    def flush(self):self.connection.commit()

    def close(self):
        self.flush()
        self.connection.close()


class EfficientB2(compact.CompactB2):
    def __init__(self,*args,**kwargs):
        super().__init__(*args,**kwargs)
        self.setup_efficient_caches(resuming=False)

    @classmethod
    def resume_compact(cls,folder,out=None):
        task=super().resume_compact(folder,out)
        task.setup_efficient_caches(resuming=True)
        return task

    def setup_efficient_caches(self,resuming):
        self.engine.__class__=EfficientReducer
        install_engine_caches(self.engine)
        bound_function_caches()
        self.completed_checks=CompletedChecks(self.out/'completed_checks.sqlite3',lambda:self.engine.version)
        self.completed_checks.begin_scope(f'{self.window}:{self.round_number}',resuming=resuming)
        self.resolved_cancellations=self.completed_checks
        self.host_seen=BoundedCache(100000,self.host_seen)
        self.host_exposed=BoundedCache(100000,self.host_exposed)
        self.host_branches=BoundedCache(20000,self.host_branches)
        self.exclusions=deque(self.exclusions,maxlen=20000)
        self._last_maintenance=perf_counter()
        self.report_options.pop('disposable_cache_limit_entries',None)
        self.report_options.update(cache_policy='bounded_LRU_no_wholesale_clears',
            completed_checks='exact_compressed_SQLite_versioned_by_rule_checkpoint',
            manual_full_garbage_collection=False,cache_limits=CACHE_LIMITS)

    def reset_overlap_checks(self):
        self.host_seen=BoundedCache(100000)
        self.host_exposed=BoundedCache(100000)
        self.host_branches=BoundedCache(20000)
        if hasattr(self,'completed_checks'):
            self.completed_checks.begin_scope(f'{self.window}:{self.round_number}')
            self.resolved_cancellations=self.completed_checks
        else:
            self.resolved_cancellations=set()

    def control(self):
        # No periodic full cache reset or full-heap garbage collection.
        # Mathematical invalidation still occurs in add/replace_parent and at
        # the beginning of the next degree or interreduction overlap pass.
        now=perf_counter()
        if not self._saving and now-getattr(self,'_last_maintenance',now)>5:
            tick=perf_counter()
            install_engine_caches(self.engine)
            self.completed_checks.flush()
            self.timings['cache_maintenance_seconds']+=perf_counter()-tick
            self._last_maintenance=perf_counter()
        return ResumableB2.control(self)

    def checkpoint(self,status,stage,full=True):
        if hasattr(self,'completed_checks'):
            tick=perf_counter()
            self.completed_checks.flush()
            self.timings['completed_check_write_seconds']+=perf_counter()-tick
            self.report_options.update(completed_check_scope=self.completed_checks.scope,
                completed_check_count=len(self.completed_checks),
                completed_check_hits=self.completed_checks.hits,
                completed_check_database_bytes=self.completed_checks.path.stat().st_size,
                historical_parent_records=len(self.engine.parents))
        return super().checkpoint(status,stage,full)


if __name__=='__main__':
    # Reuse the existing signal, checkpoint, verification and lock handling.
    compact.CompactB2=EfficientB2
    compact.main()
