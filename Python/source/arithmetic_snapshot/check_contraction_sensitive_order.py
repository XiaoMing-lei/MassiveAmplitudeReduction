"""Finite combinatorial checks; no Mathematica and no amplitude evaluation."""
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import random
import time


def chain(labels, colors):
    labels, colors = tuple(labels), tuple(colors)
    assert len(labels) == len(colors) + 1
    labels, colors = min((labels, colors), (labels[::-1], colors[::-1]))
    # square=0, angle=1; omit signs because this checks ordering only.
    return (len(colors), 0, labels, colors)


def trace(labels, colors):
    labels, colors = tuple(labels), tuple(colors)
    assert len(labels) == len(colors)
    variants = []
    for shift in range(len(labels)):
        ll = labels[shift:] + labels[:shift]
        cc = colors[shift:] + colors[:shift]
        variants.append((ll, cc))
        variants.append(((ll[0],) + ll[:0:-1], cc[::-1]))
    ll, cc = min(variants)
    return (len(colors), 1, ll, cc)


def unit_key(u):
    length, kind, labels, colors = u
    type_rank = 1 - kind  # trace < chain; stored kind remains unchanged.
    edges = []
    for j, color in enumerate(colors):
        pair = tuple(sorted((labels[j], labels[(j + 1) % len(labels)])))
        pair_key = pair if color else tuple(-x for x in pair)
        edges.append((color,) + pair_key)
    # At fixed bracket degree, ascending factor-list lex is massless grevlex.
    # Only a tied underlying bracket product reaches the routing tie-breaker.
    if kind == 1:
        assert length == 2 or (length == 4 and len(set(labels)) == 4), \
            "Normalize traces before comparing retained monomials."
        return (length, type_rank, tuple(sorted(edges)), (), ())
    return (length, type_rank, tuple(sorted(edges)), labels, colors)


def coordinates(monoms):
    bound = max((sum(u[0] for u in m) for m in monoms), default=0)
    universe = set(u for m in monoms for u in m)
    units = []
    for length in range(bound, 0, -1):
        units.extend(sorted((u for u in universe if u[0] == length),
                            key=unit_key))
    return bound, units


def key(m, basis):
    bound, units = basis
    e = Counter(m)
    return (
        sum(u[0] for u in m),
        *(sum(u[0] == length for u in m)
          for length in range(bound, 0, -1)),
        *(-sum(u[0] == length and u[1] == 1 for u in m)
          for length in range(bound, 0, -1)),
        *(-e[u] for u in units),
    )


def cmp(m, n):
    basis = coordinates([m, n])
    a, b = key(m, basis), key(n, basis)
    return (a > b) - (a < b)


def attach_at_unique_endpoint(m, label, extension_labels, extension_colors):
    """Attach a chain starting at label to the unique input endpoint there."""
    result = list(m)
    choices = [i for i, u in enumerate(m)
               if u[1] == 0 and label in (u[2][0], u[2][-1])]
    assert len(choices) == 1
    i = choices[0]
    length, kind, ll, cc = m[i]
    if ll[0] == label:
        ll, cc = ll[::-1], cc[::-1]
    assert ll[-1] == extension_labels[0] == label
    assert cc[-1] != extension_colors[0], "Only momentum-forming contractions are admissible."
    result[i] = chain(ll + tuple(extension_labels[1:]),
                      cc + tuple(extension_colors))
    return result


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


def first_sign(v):
    return next(((x > 0) - (x < 0) for x in v if x), 0)


def named_benchmarks():
    checks = {}

    def check(name, *conditions):
        assert all(conditions), name
        checks[name] = True

    # B1: a prepared momentum rule, with masses treated as coefficients.
    p = [chain([1, 5, 2], [1, 0])]
    q = [chain([1, 2], [0])]
    cp = attach_at_unique_endpoint(p, 2, [2, 4], [1])
    cq = attach_at_unique_endpoint(q, 2, [2, 4], [1])
    check("B1_degree_priority", cmp(p, q) == 1, cmp(cp, cq) == 1)

    # B2: the three pure-angle pairings with identical external content.
    high = [chain([1, 4], [1]), chain([2, 3], [1])]
    middle = [chain([1, 3], [1]), chain([2, 4], [1])]
    low = [chain([1, 2], [1]), chain([3, 4], [1])]
    check("B2_massless_schouten_order", cmp(high, middle) == 1, cmp(middle, low) == 1)
    x = [chain([5, 6], [0])]
    check("B3_tensor_product", cmp(high + x, middle + x) == 1,
          cmp(middle + x, low + x) == 1)

    p = [chain([1, 3, 4, 5, 2], [1, 0, 1, 0]), trace([3, 4], [1, 0])]
    q = [chain([1, 3, 2], [1, 0]), trace([3, 4, 5, 6], [1, 0, 1, 0])]
    check("B4_trace_below_chain", cmp(p, q) == 1)

    p = [chain([1, 6, 7, 2], [1, 0, 1]), chain([3, 4], [1])]
    q = [chain([1, 6, 2], [1, 0]), chain([3, 7, 4], [1, 0])]
    cp = attach_at_unique_endpoint(p, 3, [3, 8, 5], [0, 1])
    cq = attach_at_unique_endpoint(q, 3, [3, 8, 5], [0, 1])
    check("B5_length_profile_reversal", cmp(p, q) == 1, cmp(cp, cq) == -1)

    p = [chain([1, 3, 4, 2], [1, 0, 1])]
    q = [chain([1, 4, 3, 2], [1, 0, 1])]
    cp = attach_at_unique_endpoint(p, 1, [1, 5], [0])
    cq = attach_at_unique_endpoint(q, 1, [1, 5], [0])
    check("B6_massless_filling_preserved", cmp(p, q) == -1, cmp(cp, cq) == -1)

    p = [chain([1, 6, 7, 8, 9, 2], [1, 0, 1, 0, 1]), chain([3, 4], [1])]
    q = [chain([1, 6, 7, 8, 2], [1, 0, 1, 0]), chain([3, 7, 4], [1, 0])]
    cp = attach_at_unique_endpoint(p, 3, [3, 10], [0])
    cq = attach_at_unique_endpoint(q, 3, [3, 10], [0])
    check("B7_protected_prefix", cmp(p, q) == 1, cmp(cp, cq) == 1)

    # B8: attach both square endpoints [2 4] to the angle endpoints.
    # The first pairing merges chains; the second closes a length-two trace.
    p, q = low, middle
    cp = [chain([1, 2, 4, 3], [1, 0, 1])]
    cq = [chain([1, 3], [1]), trace([2, 4], [1, 0])]
    check("B8_endpoint_pairing_reversal", cmp(p, q) == -1, cmp(cp, cq) == 1)

    # All connected units used here obey alternating chirality.
    # B8's explicit joining uses angle/square pairs at labels 2 and 4.
    return checks


def main():
    start = time.perf_counter()
    rng = random.Random(20261020)
    assert unit_key(trace([1, 2], [1, 0])) < unit_key(chain([1, 3, 2], [1, 0]))
    # Equal degree, chain count, endpoint labels, and length histogram:
    # the side with fewer length-four traces is larger.
    trace_heavy = [trace([3, 4, 5, 6], [1, 0, 1, 0]), chain([1, 3, 2], [1, 0])]
    chain_heavy = [chain([1, 3, 4, 5, 2], [1, 0, 1, 0]), trace([3, 4], [1, 0])]
    assert cmp(trace_heavy, chain_heavy) == -1
    # Structural example: (3,1) > (2,2), but (3,3) < (4,2).
    m = [chain([1, 6, 7, 2], [1, 0, 1]), chain([3, 4], [1])]
    n = [chain([1, 6, 2], [1, 0]), chain([3, 7, 4], [1, 0])]
    cm = attach_at_unique_endpoint(m, 3, [3, 8, 5], [0, 1])
    cn = attach_at_unique_endpoint(n, 3, [3, 8, 5], [0, 1])
    assert cmp(m, n) == 1 and cmp(cm, cn) == -1
    # Different underlying products: massless grevlex preserves their order.
    a = [chain([1, 3, 4, 2], [1, 0, 1])]
    b = [chain([1, 4, 3, 2], [1, 0, 1])]
    ca = attach_at_unique_endpoint(a, 1, [1, 5], [0])
    cb = attach_at_unique_endpoint(b, 1, [1, 5], [0])
    assert cmp(b, a) == 1 and cmp(cb, ca) == 1
    # Routing-only reversal: the underlying unbold products tie.
    routing_a = [chain([1, 2, 3, 2, 1, 2], [1, 0, 1, 0, 1])]
    routing_b = [chain([1, 2, 1, 2, 3, 2], [1, 0, 1, 0, 1])]
    assert unit_key(routing_a[0])[:3] == unit_key(routing_b[0])[:3]
    routing_ca = attach_at_unique_endpoint(routing_a, 1, [1, 5], [0])
    routing_cb = attach_at_unique_endpoint(routing_b, 1, [1, 5], [0])
    assert cmp(routing_a, routing_b) == 1 and cmp(routing_ca, routing_cb) == -1
    assert cmp([chain([1, 3, 2], [1, 0])], [chain([1, 4, 2], [1, 0])]) == 1

    alphabet = [chain(pair, [color])
                for pair in combinations(range(1, 6), 2) for color in (0, 1)]
    massless_variables = sorted(alphabet, key=unit_key, reverse=True)
    pool = alphabet + [chain([1, 3, 4, 2], [1, 0, 1]),
                       chain([3, 7, 4], [1, 0]),
                       trace([1, 2], [1, 0]),
                       trace([1, 3, 4, 2], [1, 0, 1, 0])]
    product_tests = massless_tests = 0
    for _ in range(10000):
        p = rng.choices(pool, k=rng.randrange(5))
        q = rng.choices(pool, k=rng.randrange(5))
        x = rng.choices(pool, k=rng.randrange(4))
        assert cmp(p, q) == cmp(p + x, q + x)
        product_tests += 1
        p = rng.choices(alphabet, k=rng.randrange(6))
        q = rng.choices(alphabet, k=rng.randrange(6))
        ep, eq = Counter(p), Counter(q)
        kp = (len(p), *(-ep[u] for u in reversed(massless_variables)))
        kq = (len(q), *(-eq[u] for u in reversed(massless_variables)))
        assert cmp(p, q) == (kp > kq) - (kp < kq)
        massless_tests += 1

    # Compare equal external representations, lengths, and endpoint pairing.
    candidates = [
        [chain([1, *middle, 2], [1, 0, 1])]
        for middle in product(range(3, 7), repeat=2)
        if middle[0] != middle[1]
    ]
    edit_tests = prefix_protected = reversals = 0
    for p, q in combinations(candidates, 2):
        if cmp(p, q) < 0:
            p, q = q, p
        for endpoint in [1, 2]:
            for target in range(7, 10):
                x = [chain([endpoint, target], [0])]
                cp = attach_at_unique_endpoint(p, endpoint, [endpoint, target], [0])
                cq = attach_at_unique_endpoint(q, endpoint, [endpoint, target], [0])
                basis = coordinates([p, q, p + x, q + x, cp, cq])
                z = subtract(key(p, basis), key(q, basis))
                ep = subtract(key(cp, basis), key(p + x, basis))
                eq = subtract(key(cq, basis), key(q + x, basis))
                eta = subtract(ep, eq)
                result = tuple(i + j for i, j in zip(z, eta))
                assert result == subtract(key(cp, basis), key(cq, basis))
                assert first_sign(result) == cmp(cp, cq)
                decisive = next(i for i, v in enumerate(z) if v)
                if all(v == 0 for v in eta[:decisive + 1]):
                    assert cmp(cp, cq) == 1
                    prefix_protected += 1
                reversals += cmp(cp, cq) == -1
                edit_tests += 1

    # Nonvacuous prefix-protection tests: the decisive length-five component
    # stays untouched, while all modified components have lengths below five.
    p = [chain([1, 6, 7, 8, 9, 2], [1, 0, 1, 0, 1]), chain([3, 4], [1])]
    q = [chain([1, 6, 7, 8, 2], [1, 0, 1, 0]), chain([3, 7, 4], [1, 0])]
    for target in range(10, 30):
        x = [chain([3, target], [0])]
        cp = attach_at_unique_endpoint(p, 3, [3, target], [0])
        cq = attach_at_unique_endpoint(q, 3, [3, target], [0])
        basis = coordinates([p, q, p + x, q + x, cp, cq])
        z = subtract(key(p, basis), key(q, basis))
        eta = subtract(subtract(key(cp, basis), key(p + x, basis)),
                       subtract(key(cq, basis), key(q + x, basis)))
        decisive = next(i for i, v in enumerate(z) if v)
        assert all(v == 0 for v in eta[:decisive + 1])
        assert cmp(p, q) == cmp(cp, cq) == 1
        prefix_protected += 1
        edit_tests += 1

    report = {
        "scope": "Combinatorial checks only; not amplitude identities or confluence.",
        "mathematica_started": False,
        "equal_length_type_order": "trace < chain",
        "context_restriction": "same particle label and opposite chirality",
        "unit_filling_order": "unbold massless grevlex, then routing tie-breaker",
        "trace_order_checks": 2,
        "named_benchmarks": named_benchmarks(),
        "length_profile_reversal": True,
        "canonical_traversal_reversal": True,
        "tensor_product_comparisons": product_tests,
        "massless_grevlex_comparisons": massless_tests,
        "context_edit_comparisons": edit_tests,
        "prefix_protected_contexts": prefix_protected,
        "reversed_contexts_in_filling_sample": reversals,
        "seconds": time.perf_counter() - start,
    }
    output = Path(__file__).with_name("ContractionSensitiveMonomialOrder_checks.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
