"""Fresh v3.2 construction with common-overlap degree at most D+1.

The explicit finite-search bound is applied after determinant normalization,
before preparing the two contextual identities. Complete identities are never
term-truncated. Parent/remainder degree remains D. All admitted contextual LM
tests, reductions and dependency reopening use the prior runner. The final
offline preparation of encountered descendants is omitted by user instruction;
amplitude reduction still prepares requested contextual RHSs on demand.
"""
from pathlib import Path
from time import perf_counter
import run_phase_timed_construction as timed
import shared_dependency_storage as sharing
import n_point_mass_arithmetic as masses

c = timed.base.compact.original.c
b, p, direct = c.b, c.p, c.direct


class OverlapCappedConstruction(timed.PhaseTimedConstruction):
    def __init__(self, n, degree, out, *args, **kwargs):
        if n > 4:
            masses.install()
        self.overlap_degree_cap = degree+1
        super().__init__(n, degree, out, *args, **kwargs)
        self.set_scope()

    def set_scope(self):
        self.report_options.update(
            revision='incremental_route_pool_overlap_D_plus_1_parent_only',
            common_input_degree_cap=self.overlap_degree_cap,
            overlap_cap_definition='Degree of the complete normalized common tensor monomial, before cancellation and common-factor removal',
            parent_and_output_degree_cap=self.degree,
            common_overlap_cutoff_is_not_parent_cutoff=True,
            algorithm_unchanged_from='Shared-storage v3.2 except requested common-overlap cap D+1 and omission of final offline contextual preparation',
            final_context_preparation=False,
            prepared_descendant_table=False,
            amplitude_context_preparation='Requested RHS preparation at query time remains required',
            completion_scope='All queued work from admitted parent overlaps and incremental propagation; excludes extra searches induced by the omitted final context-preparation pass',
            finite_scope_only=True,
            above_bound_work='All admitted S tasks are reduced, including S degrees above D; only common overlaps above D+1 are excluded',
            frame_generation='Enumerates original overlap frames; filters normalized common inputs before contextual substitution',
            raw_graph_degree_pruning=False)

    def install_store(self, migrate=False):
        super().install_store(migrate)
        self.set_scope()

    def run(self):
        if self.phase == 'degree_stages':
            for stage in range(self.completed_stage+1, self.degree+1):
                tick = perf_counter()
                self.stabilize(stage)
                self.rounds.append({'parent_degree': stage, 'seconds_this_segment': perf_counter()-tick,
                                    'active_parents': sum(r['active'] for r in self.engine.parents),
                                    'provisional_while_higher_S_polynomials_pending': True})
                self.completed_stage = stage
                self.checkpoint('degree_stage_finished', {'parent_degree': stage})
            self.phase = 'above_bound_queue'
        if self.phase == 'above_bound_queue':
            self.stabilize(self.degree, allow_higher=True)
            self.phase = 'complete'
        assert self.phase == 'complete', 'Only this parent-only workflow may be resumed'
        assert not self.pair_heap and not self.s_heap and self.propagation_state is None
        assert self.timings['context_preparation_seconds'] == 0
        c.bp.save(self.out/'final_groups.json', [
            {'id': r['id'], 'family': r['family'], 'original': r['raw'] is not None,
             'group': c.old.prior.rule_group(r['row']) if r['row'] else 2,
             'degree': max(map(p.degree, r['row']), default=2)}
            for r in self.engine.parents if r['active']])
        return self.checkpoint('completed_capped_parent_queue', {'parent_degree': self.degree})

    def register_route(self, head, row, source, origin):
        if not self.admitted_head(head):
            self.stats['route_requests_above_overlap_cap'] += 1
            return None
        return super().register_route(head, row, source, origin)

    def admitted_head(self, head):
        return p.degree(head) <= self.overlap_degree_cap

    def queue_route_difference(self, head, left_id, right_id, reopen=False):
        assert p.degree(head) <= self.overlap_degree_cap
        return super().queue_route_difference(head, left_id, right_id, reopen=reopen)

    def process_pair(self, item):
        self.process_capped_pair(item)
        self.boundary()

    def process_capped_pair(self, item):
        degree, i, j, stamp = item
        self.pair_scheduled.discard(stamp)
        if stamp != self.pair_stamp(i, j) or not all(self.engine.parents[k]['active'] for k in (i, j)):
            self.stats['obsolete_pair_versions_skipped'] += 1
            return
        if stamp in self.pair_done:
            return
        self.current_pair = item
        self.stage = {'parent_degree': self.window, 'left_parent': i, 'right_parent': j,
                      'phase': 'direct_parent_overlaps'}
        self.stats['parent_pairs'] += 1
        for ti, a in self.engine.parent_patterns(self.engine.parents[i]):
            for tj, z in self.engine.parent_patterns(self.engine.parents[j]):
                tick = perf_counter()
                for graph, shared, ap, zp, extra, keys in direct.overlap_frames(a, z):
                    self.timings['input_generation_seconds'] += perf_counter()-tick
                    self.control()
                    self.stats['overlap_frames_after_dummy_relabel_dedup'] += 1
                    # Do not prune by raw graph length: determinant preparation
                    # can lower its tensor degree. Keep both original placements.
                    image = b.normalize_graph(*graph)
                    eligible = {head for head in image if self.admitted_head(head)}
                    self.stats['normalized_common_terms_above_overlap_cap'] += len(image)-len(eligible)
                    if image and not eligible:
                        self.stats['overlap_frames_excluded_by_cap'] += 1
                    if eligible:
                        self.stats['overlap_frames_admitted_by_cap'] += 1
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
                self.timings['input_generation_seconds'] += perf_counter()-tick
        self.pair_done.add(stamp)
        self.current_pair = None


if __name__ == '__main__':
    sharing.install()
    OverlapCappedConstruction.entrypoint = str(Path(__file__).resolve())
    timed.base.compact.main(runner_class=OverlapCappedConstruction)
