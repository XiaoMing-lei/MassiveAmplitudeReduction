"""Unchanged resumable construction with explicit phase timing records.

This is measurement, not an optimization or a change of mathematical scope.
Standalone degree-D completion separates stages, higher-S cleanup, and final
context preparation. Checkpoint/store times remain separately recorded.
"""
import json
from time import perf_counter
import run_resumable_propagation as base


class PhaseTimedConstruction(base.ResumableOvernight):
    def stabilize(self,stage,allow_higher=False):
        phase=self.phase
        before=dict(self.timings);counts=dict(self.stats)
        tick=perf_counter();status='interrupted'
        try:
            result=super().stabilize(stage,allow_higher=allow_higher)
            status='completed'
            return result
        finally:
            record={'phase':phase,'stage':stage,'allow_higher':allow_higher,
                    'status':status,'elapsed_seconds':perf_counter()-tick,
                    'timer_deltas':{k:v-before.get(k,0) for k,v in self.timings.items()
                                    if v!=before.get(k,0)},
                    'counter_deltas':{k:v-counts.get(k,0) for k,v in self.stats.items()
                                      if v!=counts.get(k,0)},
                    'active_parents':sum(r['active'] for r in self.engine.parents)}
            with (self.out/'phase_timings.jsonl').open('a',encoding='utf-8') as stream:
                stream.write(json.dumps(record)+'\n')


if __name__=='__main__':
    from pathlib import Path
    PhaseTimedConstruction.entrypoint=str(Path(__file__).resolve())
    base.compact.main(runner_class=PhaseTimedConstruction)
