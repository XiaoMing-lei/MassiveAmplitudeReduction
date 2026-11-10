"""Share immutable dependency identifiers; preserve all mathematical records.

This module is opt-in. The ordinary production wrapper remains unchanged.
One processed S task supplies one compact Key to all of its parent indexes.
The loader also shares equal immutable Keys without changing hashes or values.
"""
import gc
import gzip
import pickle
import compressed_polynomial_keys as keys
import construct_route_pool as construction


def process_task_with_shared_key(self, item):
    # Same base reduction and dependency traversal as RoutePoolConstruction.
    super(construction.RoutePoolConstruction, self).process_task(item)
    task = self.tasks[item[2]]
    dependencies = set()
    for name in ('left_source', 'right_source'):
        dependencies.update(self.source_parents(task['proof'][name]))
    for step in task['steps']:
        dependencies.update(self.source_parents(step['source']))
    key = keys.pack(item[2])
    for pid in dependencies:
        self.checks_by_parent[pid].add(key)


class SharedKeyUnpickler(pickle.Unpickler):
    def __init__(self, stream):
        super().__init__(stream)
        self.key_pool = {}

    def restore_key(self, data):
        old = self.key_pool.get(data)
        if old is not None:
            return old
        result = keys.restore_key(data)
        self.key_pool[data] = result
        return result

    def find_class(self, module, name):
        if module == 'compressed_polynomial_keys' and name == 'restore_key':
            return self.restore_key
        return super().find_class(module, name)


def load_shared(path):
    enabled = gc.isenabled()
    if enabled:
        gc.disable()
    try:
        with gzip.open(path, 'rb') as stream:
            reader = SharedKeyUnpickler(stream)
            result = reader.load()
            reader.key_pool.clear()
            del reader
            return result
    finally:
        if enabled:
            gc.enable()


def install():
    construction.RoutePoolConstruction.process_task = process_task_with_shared_key
    import checkpoint_io
    checkpoint_io.load = load_shared
