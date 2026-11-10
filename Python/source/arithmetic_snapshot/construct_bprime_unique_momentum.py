"""B' completion using the single prescribed LM of each original M identity.

Nonleading momentum terms seed neither overlaps nor contextual replacements.
Original M/S identities, Schouten options, degree staging and proof records are
preserved. No basis construction or exhaustive amplitude scan is performed.
"""
import argparse
from construct_bprime_lm_gated import LMGatedConstruction


class UniqueMomentumConstruction(LMGatedConstruction):
    def __init__(self, n, degree, seconds=600, tag='_unique_momentum'):
        super().__init__(n, degree, seconds, tag)
        # No matching has run during initialization, so there are no cached
        # nonleading M occurrences to invalidate when selecting the policy.
        self.engine.unique_momentum_lm = True
        self.report_options = {'unique_momentum_lm': True,
                               'momentum_pattern_count': n*n}
        self.report_options['momentum_policy'] = (
            'Each original M_ij uses only the smallest momentum label unequal '
            'to its endpoints. Other M terms seed no descendants or overlaps. '
            'The runtime matcher rejects their occurrences before substitution. '
            'Keep the actual-context decreasing-order check.')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--particles', type=int, default=4)
    ap.add_argument('--degree', type=int, default=4)
    ap.add_argument('--seconds', type=float, default=600)
    ap.add_argument('--tag', default='_unique_momentum')
    args = ap.parse_args()
    task = UniqueMomentumConstruction(args.particles, args.degree, args.seconds, args.tag)
    try:
        task.run()
    except TimeoutError:
        task.checkpoint('time_limit_partial', task.stage)


if __name__ == '__main__':
    main()
