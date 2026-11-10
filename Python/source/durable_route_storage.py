"""Lossless disk storage for authoritative route records (not a memo cache).

Mutable records remain pinned during an algebraic operation. At its safe
boundary they are written in full before being released. Iteration preserves
insertion order; keys are exact encodings, with no probabilistic fingerprints.
"""
from collections.abc import MutableMapping, Sequence
import marshal
from pathlib import Path
import pickle
import sqlite3
import zlib


def key_bytes(key):
    # Marshal v2 does not encode object sharing: equal immutable keys have
    # identical bytes even after separate checkpoint unpickling.
    return zlib.compress(marshal.dumps(key, 2), 1)


class Store:
    def __init__(self, path, readonly=False):
        self.path = Path(path)
        self.readonly = readonly
        self.connection = (sqlite3.connect(self.path.resolve().as_uri()+'?mode=ro&immutable=1',uri=True)
                           if readonly else sqlite3.connect(self.path))
        if not readonly:
            self.connection.execute('PRAGMA journal_mode=WAL')
            self.connection.execute('PRAGMA synchronous=NORMAL')
        self.connection.execute('PRAGMA cache_size=-16384')
        self.collections = {}
        self.flushes = 0

    def collection(self, name, sequence=False):
        if name not in self.collections:
            assert name.isidentifier()
            if not self.readonly:
                self.connection.execute(f'CREATE TABLE IF NOT EXISTS {name} '
                    '(id INTEGER PRIMARY KEY, key BLOB NOT NULL UNIQUE, value BLOB NOT NULL)')
            cls = DiskSequence if sequence else DiskMap
            self.collections[name] = cls(self, name)
        return self.collections[name]

    def flush(self):
        for collection in self.collections.values():
            collection.flush()
        self.connection.commit()
        self.flushes += 1

    def backup(self, target):
        self.flush()
        destination = sqlite3.connect(target)
        try:
            self.connection.backup(destination)
        finally:
            destination.close()

    def close(self):
        self.flush()
        self.connection.close()


class DiskMap(MutableMapping):
    def __init__(self, store, name):
        self.store, self.name = store, name
        self.hot = {}
        self.count = store.connection.execute(f'SELECT count(*) FROM {name}').fetchone()[0]

    def __len__(self):
        return self.count

    def __contains__(self, key):
        if key in self.hot:
            return True
        return self.store.connection.execute(f'SELECT 1 FROM {self.name} WHERE key=?',
            (key_bytes(key),)).fetchone() is not None

    def __getitem__(self, key):
        if key not in self.hot:
            row = self.store.connection.execute(f'SELECT value FROM {self.name} WHERE key=?',
                (key_bytes(key),)).fetchone()
            if row is None:
                raise KeyError(key)
            self.hot[key] = pickle.loads(zlib.decompress(row[0]))
        return self.hot[key]

    def __setitem__(self, key, value):
        if self.store.readonly:raise TypeError('Read-only checkpoint')
        if key not in self:
            # Reserve insertion order before any later key can be inserted.
            self.store.connection.execute(f'INSERT INTO {self.name}(key,value) VALUES (?,?)',
                (key_bytes(key), b''))
            self.count += 1
        self.hot[key] = value

    def __delitem__(self, key):
        if self.store.readonly:raise TypeError('Read-only checkpoint')
        if key not in self:
            raise KeyError(key)
        self.hot.pop(key, None)
        self.store.connection.execute(f'DELETE FROM {self.name} WHERE key=?', (key_bytes(key),))
        self.count -= 1

    def __iter__(self):
        for row in self.store.connection.execute(f'SELECT key FROM {self.name} ORDER BY id'):
            yield marshal.loads(zlib.decompress(row[0]))

    def flush(self):
        if not self.hot:
            return
        if self.store.readonly:
            self.hot.clear();return
        self.store.connection.executemany(f'UPDATE {self.name} SET value=? WHERE key=?',
            ((zlib.compress(pickle.dumps(value, protocol=5), 1), key_bytes(key))
             for key, value in self.hot.items()))
        self.hot.clear()

    def descriptor(self):
        return {'disk_collection': self.name, 'sequence': False, 'count': self.count}


class DiskSequence(DiskMap, Sequence):
    def append(self, value):
        self[len(self)] = value

    def __iter__(self):
        for index in range(len(self)):
            yield self[index]

    def __getitem__(self, index):
        if isinstance(index, slice):
            return [self[k] for k in range(*index.indices(len(self))) ]
        if index < 0:
            index += len(self)
        if index >= len(self):
            raise IndexError(index)
        return super().__getitem__(index)

    def descriptor(self):
        return {'disk_collection': self.name, 'sequence': True, 'count': self.count}


FIELDS = ('pools', 'routes', 'route_edges', 'tasks')


def attach(task, path, migrate=False, verify=True):
    store = Store(path)
    task.disk_store = store
    for name in FIELDS:
        previous = getattr(task, name)
        sequence = name in ('routes', 'route_edges')
        collection = store.collection(name, sequence)
        if migrate:
            assert not len(collection), 'Migration requires a fresh store'
            keys = range(len(previous)) if sequence else list(previous)
            for ordinal, key in enumerate(keys):
                value = previous[key]
                collection[key] = value
                if verify:
                    assert pickle.loads(zlib.decompress(zlib.compress(pickle.dumps(value, 5), 1))) == value
                if sequence:
                    previous[key] = None
                else:
                    del previous[key]
                if ordinal % 1000 == 999:
                    store.flush()
            store.flush()
        elif isinstance(previous, dict) and 'disk_collection' in previous:
            assert previous['disk_collection'] == name and previous['count'] == len(collection)
        setattr(task, name, collection)
    return store
