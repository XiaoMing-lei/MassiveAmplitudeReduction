"""Bulk checkpoint loading without repeated collection of its live object graph."""
import gc
import gzip
import pickle


def load(path):
    enabled=gc.isenabled()
    if enabled:gc.disable()
    try:
        with gzip.open(path,'rb') as stream:return pickle.load(stream)
    finally:
        if enabled:gc.enable()
