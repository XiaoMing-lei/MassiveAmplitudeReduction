"""Post-reduction classification by highest-degree unbolded products.

Group 2 iff all maximum-bracket-degree terms share one unbolded product;
otherwise group 1. This is independent of proof ancestry. The existing
matcher is reused for this bounded diagnostic, not a completed prepared-A
application package. No catalog construction is performed here.
"""
import degree_staged_reduction as previous

t = previous.t
b, bp, p = t.b, t.bp, t.p


def rule_group(row):
    if not row:
        raise ValueError('A zero prepared polynomial has no oriented replacement')
    degree = max(map(p.degree, row))
    products = {t.base.ordering.unbolded(mon) for mon in row
                if p.degree(mon) == degree}
    return 2 if len(products) == 1 else 1


class UnboldedGroupReducer(previous.DegreeStagedReducer):
    def group_actions(self, mon, group, excluded_identities=frozenset()):
        result = []
        for row, source in self.actions(mon):
            if excluded_identities and p.encode(p.primitive(row)[0]) in excluded_identities:
                continue
            if rule_group(row) == group:
                source = {**source,
                    'historical_ancestry_group': self.source_group(source),
                    'application_group': group,
                    'classification': 'maximum_degree_unbolded_products'}
                result.append((row, source))
        return result


def load_unbolded_groups(data, archive_path=None):
    engine = previous.load_degree_staged(data, archive_path)
    engine.__class__ = UnboldedGroupReducer
    return engine
