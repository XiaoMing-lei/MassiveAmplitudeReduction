"""Group 1 then group 2 at each bracket degree, descending in degree.

Lower-degree corrections start their own two stages. A same-degree return
is reported, never silently taken. Parent identities and order are frozen.
Historical strict whole-polynomial reducers remain available unchanged.
"""
import two_stage_interreduction as t

b, bp, p = t.b, t.bp, t.p


class DegreeStagedReducer(t.TwoStageReducer):
    def reduce(self, row, only_m=False, reverse=False, trace=False,
               max_steps=200000, excluded_identities=frozenset(), diagnostic=False):
        if only_m:
            return super().reduce(row, only_m=True, reverse=reverse,
                                  trace=trace, max_steps=max_steps,
                                  excluded_identities=excluded_identities)
        pending, out, den, steps = dict(row), {}, b.ONE, []
        self.last_degree_report = {'degrees': [], 'same_degree_gaps': []}
        count = 0
        while pending:
            degree = max(map(p.degree, pending))
            block = {'degree': degree, 'group1_steps': 0, 'group2_steps': 0}
            for group in (1, 2):
                untouched = {}
                while any(p.degree(m) == degree for m in pending):
                    if hasattr(self, 'budget_check'):
                        self.budget_check()
                    head = max((m for m in pending if p.degree(m) == degree),
                               key=b.mkey)
                    actions = self.group_actions(head, group, excluded_identities)
                    if not actions:
                        b.add_term(untouched, head, pending.pop(head))
                        continue
                    rel, source = actions[-1 if reverse else 0]
                    assert max(rel, key=b.mkey) == head
                    assert all(b.mkey(m) < b.mkey(head) for m in rel if m != head)
                    assert all(p.degree(m) <= degree for m in rel)
                    ah, rh = pending[head], rel[head]
                    pending = p.subtract(pending, ah, rel, rh)
                    if rh != b.ONE:
                        out = bp.poly_scale(out, rh)
                        untouched = bp.poly_scale(untouched, rh)
                        den = b.pmul(den, rh)
                    count += 1
                    block[f'group{group}_steps'] += 1
                    if trace:
                        steps.append({'input': head,
                            'source': {**source, 'origin_group': group},
                            'identity': rel, 'input_coefficient': ah,
                            'leading_coefficient': rh, 'stage': group,
                            'degree_stage': degree,
                            'top_behavior': t.base.ordering.top_behavior(rel)})
                    if count > max_steps:
                        raise RuntimeError('Reduction step limit')
                for mon, coeff in untouched.items():
                    b.add_term(pending, mon, coeff)
            # Only the final same-degree polynomial matters: intermediate
            # offending terms can cancel while group 2 finishes.
            for mon in sorted((m for m in pending if p.degree(m) == degree),
                              key=b.mkey, reverse=True):
                actions = self.group_actions(mon, 1, excluded_identities)
                if actions:
                    self.last_degree_report['same_degree_gaps'].append({
                        'degree': degree, 'monomial': mon,
                        'group1_sources': [source for _, source in actions]})
                b.add_term(out, mon, pending.pop(mon))
            self.last_degree_report['degrees'].append(block)
        if self.last_degree_report['same_degree_gaps'] and not diagnostic:
            self.last_stage_gap = self.last_degree_report['same_degree_gaps'][0]
            raise t.base.StageCoverageGap(
                'Group 2 left a group-1 match at the same bracket degree; '
                'no same-degree return was performed. Use diagnostic=True '
                'only to inspect the unfinished expression and its certificate.')
        return out, den, steps


def load_degree_staged(data, archive_path=None):
    engine = t.load_two_stage(data, archive_path)
    engine.__class__ = DegreeStagedReducer
    return engine
