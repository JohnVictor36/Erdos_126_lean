#!/usr/bin/env python3
"""Computational stress tests for the Erdos 126 square-root proof.

This is an independent executable model of four arithmetic/combinatorial
interfaces used by the Lean development:

* the gcd-and-parity normalization of a sum and a difference;
* one simultaneous p-adic involution at every positive threshold;
* the exact biased-selection expectation and its 1/8 lower bound;
* the normalized logarithmic permutation-cost bound with constant 6.

The tests are finite evidence, not a substitute for the proofs.  On the first
failure an AssertionError contains a complete counterexample certificate.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from fractions import Fraction
from functools import lru_cache
from typing import Iterable, Sequence


PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)


def vp(n: int, p: int) -> int:
    """The finite Nat-style p-adic valuation (zero is used only diagonally)."""
    if n == 0:
        return 0
    ans = 0
    while n % p == 0:
        n //= p
        ans += 1
    return ans


def normalizer(a: int, b: int) -> int:
    g = math.gcd(a, b)
    x, y = a // g, b // g
    return g * (2 if x % 2 == 1 and y % 2 == 1 else 1)


def normalized_sum(a: int, b: int) -> int:
    return (a + b) // normalizer(a, b)


def normalized_dist(a: int, b: int) -> int:
    return abs(a - b) // normalizer(a, b)


def normalized_sum_val(p: int, a: int, b: int) -> int:
    return vp(normalized_sum(a, b), p)


def normalized_diff_val(p: int, a: int, b: int) -> int:
    return vp(normalized_dist(a, b), p)


def formula_normalizer_val(p: int, a: int, b: int) -> int:
    va, vb = vp(a, p), vp(b, p)
    return min(va, vb) + (1 if p == 2 and va == vb else 0)


def p_unit(p: int, a: int) -> int:
    return a // (p ** vp(a, p))


def p_unit_side(p: int, a: int) -> bool:
    q = 4 if p == 2 else p
    r = p_unit(p, a) % q
    return r < q - r


def ordered_mass(values: Sequence[int], p: int, kind: str) -> int:
    val = normalized_sum_val if kind == "sum" else normalized_diff_val
    return sum(val(p, a, b) for a in values for b in values if a != b)


def max_score_involution(values: Sequence[int], p: int) -> tuple[int, ...]:
    """A maximum-base-4 matching, with fixed points allowed."""
    n = len(values)
    u = [[normalized_sum_val(p, values[i], values[j]) for j in range(n)]
         for i in range(n)]

    @lru_cache(maxsize=None)
    def solve(mask: int) -> tuple[int, tuple[tuple[int, int], ...]]:
        if mask == 0:
            return 0, ()
        i_bit = mask & -mask
        i = i_bit.bit_length() - 1
        rest = mask ^ i_bit
        best_score, best_pairs = solve(rest)  # i is fixed
        candidates = rest
        while candidates:
            j_bit = candidates & -candidates
            j = j_bit.bit_length() - 1
            tail_score, tail_pairs = solve(rest ^ j_bit)
            score = tail_score + 2 * (4 ** u[i][j])
            if score > best_score:
                best_score = score
                best_pairs = tail_pairs + ((i, j),)
            candidates ^= j_bit
        return best_score, best_pairs

    _, pairs = solve((1 << n) - 1)
    tau = list(range(n))
    for i, j in pairs:
        tau[i], tau[j] = j, i
    return tuple(tau)


def check_involution_thresholds(values: Sequence[int], p: int) -> dict[str, int]:
    n = len(values)
    tau = max_score_involution(values, p)
    assert all(tau[tau[i]] == i for i in range(n)), (values, p, tau)
    u = [[normalized_sum_val(p, values[i], values[j]) for j in range(n)]
         for i in range(n)]
    d = [[normalized_diff_val(p, values[i], values[j]) for j in range(n)]
         for i in range(n)]
    max_level = max((u[i][j] for i in range(n) for j in range(n) if i != j),
                    default=0)
    min_threshold_margin = 10**30
    for level in range(1, max_level + 1):
        U = sum(u[i][j] >= level for i in range(n) for j in range(n) if i != j)
        D = sum(d[i][j] >= level for i in range(n) for j in range(n) if i != j)
        M = sum(tau[i] != i and u[i][tau[i]] >= level for i in range(n))
        margin = D + M - U
        min_threshold_margin = min(min_threshold_margin, margin)
        assert margin >= 0, {
            "kind": "threshold", "values": values, "p": p, "tau": tau,
            "level": level, "U": U, "D": D, "M": M,
        }
    U_weight = sum(u[i][j] for i in range(n) for j in range(n) if i != j)
    D_weight = sum(d[i][j] for i in range(n) for j in range(n) if i != j)
    M_weight = sum(u[i][tau[i]] for i in range(n) if tau[i] != i)
    assert U_weight <= D_weight + M_weight, {
        "kind": "weighted", "values": values, "p": p, "tau": tau,
        "U": U_weight, "D": D_weight, "M": M_weight,
    }
    return {
        "U": U_weight,
        "D": D_weight,
        "M": M_weight,
        "weighted_margin": D_weight + M_weight - U_weight,
        "threshold_margin": 0 if min_threshold_margin == 10**30 else min_threshold_margin,
    }


def retained(orientation: bool, side: bool, label: int) -> bool:
    return label != 0 if orientation == side else label == 0


def direct_expected_slack(values: Sequence[int], p: int,
                          tau: Sequence[int]) -> Fraction:
    """Enumerate all 2*4^n points of the finite product experiment."""
    n = len(values)
    sides = [p_unit_side(p, a) for a in values]
    u = [[normalized_sum_val(p, values[i], values[j]) for j in range(n)]
         for i in range(n)]
    d = [[normalized_diff_val(p, values[i], values[j]) for j in range(n)]
         for i in range(n)]
    total = 0
    sample_count = 0
    for orientation in (False, True):
        for labels in itertools.product(range(4), repeat=n):
            selected = [retained(orientation, sides[i], labels[i]) for i in range(n)]
            D = sum(d[i][j] for i in range(n) for j in range(n)
                    if i != j and selected[i] and selected[j])
            U = sum(u[i][j] for i in range(n) for j in range(n)
                    if i != j and selected[i] and selected[j])
            M = sum(u[i][tau[i]] for i in range(n)
                    if tau[i] != i and selected[i] and selected[tau[i]])
            total += D + M - U
            sample_count += 1
    return Fraction(total, sample_count)


def check_heavy_expectation(values: Sequence[int], p: int,
                            direct: bool) -> dict[str, object]:
    tau = max_score_involution(values, p)
    U = ordered_mass(values, p, "sum")
    D = ordered_mass(values, p, "diff")
    M = sum(normalized_sum_val(p, values[i], values[tau[i]])
            for i in range(len(values)) if tau[i] != i)
    expected = Fraction(5 * D + 3 * M - 3 * U, 16)
    target = Fraction(D, 8)
    assert expected >= target, {
        "kind": "heavy-expectation", "values": values, "p": p,
        "tau": tau, "U": U, "D": D, "M": M,
        "expected": str(expected), "target": str(target),
    }
    if direct:
        enumerated = direct_expected_slack(values, p, tau)
        assert enumerated == expected, {
            "kind": "heavy-direct", "values": values, "p": p,
            "tau": tau, "formula": str(expected), "enumerated": str(enumerated),
        }
    return {
        "U": U, "D": D, "M": M,
        "margin_numerator_over_16": 3 * (D + M - U),
        "direct": direct,
    }


def reduced_product(a: int, b: int) -> int:
    g = math.gcd(a, b)
    return (a // g) * (b // g)


def metric_ratio(values: Sequence[int], perm: Sequence[int]) -> float:
    n = len(values)
    w = [[0.0 if i == j else math.log(normalized_sum(values[i], values[j]))
          for j in range(n)] for i in range(n)]
    total = sum(sum(row) for row in w)
    cost = sum(w[i][perm[i]] for i in range(n))
    return 0.0 if total == 0 else n * cost / total


def check_metric(values: Sequence[int], perms: Iterable[Sequence[int]]) -> tuple[float, tuple[int, ...]]:
    n = len(values)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                left = 1 if i == k else reduced_product(values[i], values[k])
                first = 1 if i == j else reduced_product(values[i], values[j])
                second = 1 if j == k else reduced_product(values[j], values[k])
                assert left <= first * second, {
                    "kind": "metric-triangle", "values": values,
                    "triple": (i, j, k), "left": left,
                    "right": first * second,
                }
    best = (-1.0, tuple(range(n)))
    for perm0 in perms:
        perm = tuple(perm0)
        assert sorted(perm) == list(range(n))
        ratio = metric_ratio(values, perm)
        assert ratio <= 6.0 + 1e-12, {
            "kind": "metric-constant", "values": values,
            "perm": perm, "ratio": ratio,
        }
        if ratio > best[0]:
            best = (ratio, perm)
    return best


def run(quick: bool) -> dict[str, object]:
    rng = random.Random(12620260902)
    counters = {
        "normalization_pairs": 0,
        "normalization_valuation_checks": 0,
        "padic_instances": 0,
        "padic_threshold_levels": 0,
        "heavy_formula_instances": 0,
        "heavy_full_sample_instances": 0,
        "heavy_full_sample_points": 0,
        "metric_sets": 0,
        "metric_permutations": 0,
        "metric_triangles": 0,
    }

    normalization_limit = 120 if quick else 350
    for a in range(1, normalization_limit + 1):
        for b in range(1, normalization_limit + 1):
            q = normalizer(a, b)
            ns, nd = normalized_sum(a, b), normalized_dist(a, b)
            assert ns * q == a + b, (a, b, q, ns)
            assert nd * q == abs(a - b), (a, b, q, nd)
            assert math.gcd(ns, nd) == 1, (a, b, ns, nd)
            counters["normalization_pairs"] += 1
            for p in PRIMES[:5]:
                nv = formula_normalizer_val(p, a, b)
                assert normalized_sum_val(p, a, b) == vp(a + b, p) - nv
                if a != b:
                    assert normalized_diff_val(p, a, b) == vp(abs(a - b), p) - nv
                counters["normalization_valuation_checks"] += 1

    # Exhaustive small sets and primes.  This is the main counterexample search.
    exhaustive_top = 9 if quick else 11
    exhaustive_max_card = 6 if quick else 7
    exhaustive_sets: list[tuple[int, ...]] = []
    for n in range(2, exhaustive_max_card + 1):
        exhaustive_sets.extend(itertools.combinations(range(1, exhaustive_top + 1), n))

    min_weighted_margin = 10**30
    min_heavy_margin = 10**30
    nontrivial_heavy_equality_witness = None
    direct_per_card = 2 if quick else 6
    direct_counts: dict[int, int] = {}
    for set_index, values in enumerate(exhaustive_sets):
        for p in PRIMES[:4]:
            info = check_involution_thresholds(values, p)
            counters["padic_instances"] += 1
            counters["padic_threshold_levels"] += max(
                (normalized_sum_val(p, a, b) for a in values for b in values if a != b),
                default=0)
            min_weighted_margin = min(min_weighted_margin, info["weighted_margin"])
            do_direct = (len(values) <= 7 and info["U"] > 0 and
                         direct_counts.get(len(values), 0) < direct_per_card)
            hinfo = check_heavy_expectation(values, p, do_direct)
            counters["heavy_formula_instances"] += 1
            min_heavy_margin = min(min_heavy_margin, hinfo["margin_numerator_over_16"])
            if (nontrivial_heavy_equality_witness is None and hinfo["D"] > 0 and
                    hinfo["margin_numerator_over_16"] == 0):
                nontrivial_heavy_equality_witness = {
                    "values": values, "p": p,
                    "U": hinfo["U"], "D": hinfo["D"], "M": hinfo["M"],
                }
            if do_direct:
                direct_counts[len(values)] = direct_counts.get(len(values), 0) + 1
                counters["heavy_full_sample_instances"] += 1
                counters["heavy_full_sample_points"] += 2 * (4 ** len(values))

    # Large-height random sets test the arithmetic independently of small ranges.
    random_instances = 90 if quick else 450
    for trial in range(random_instances):
        n = rng.randint(2, 9 if quick else 13)
        cap = 10**6 if quick else 10**12
        values = tuple(sorted(rng.sample(range(1, cap), n)))
        p = rng.choice(PRIMES)
        info = check_involution_thresholds(values, p)
        counters["padic_instances"] += 1
        counters["padic_threshold_levels"] += max(
            (normalized_sum_val(p, a, b) for a in values for b in values if a != b),
            default=0)
        min_weighted_margin = min(min_weighted_margin, info["weighted_margin"])
        do_direct = trial < (5 if quick else 20) and n <= 7
        hinfo = check_heavy_expectation(values, p, do_direct)
        counters["heavy_formula_instances"] += 1
        min_heavy_margin = min(min_heavy_margin, hinfo["margin_numerator_over_16"])
        if do_direct:
            counters["heavy_full_sample_instances"] += 1
            counters["heavy_full_sample_points"] += 2 * (4 ** n)

    # Exhaust all permutations of small configurations for the metric constant.
    metric_top = 8 if quick else 10
    metric_max_card = 6 if quick else 7
    best_metric = (-1.0, (), ())
    metric_max_by_card: dict[int, tuple[float, tuple[int, ...], tuple[int, ...]]] = {}
    for n in range(2, metric_max_card + 1):
        perms = list(itertools.permutations(range(n)))
        for values in itertools.combinations(range(1, metric_top + 1), n):
            ratio, perm = check_metric(values, perms)
            counters["metric_sets"] += 1
            counters["metric_permutations"] += len(perms)
            counters["metric_triangles"] += n ** 3
            if ratio > best_metric[0]:
                best_metric = (ratio, values, perm)
            if n not in metric_max_by_card or ratio > metric_max_by_card[n][0]:
                metric_max_by_card[n] = (ratio, values, perm)

    random_metric_sets = 60 if quick else 250
    random_perm_count = 30 if quick else 100
    for _ in range(random_metric_sets):
        n = rng.randint(2, 10 if quick else 14)
        values = tuple(sorted(rng.sample(range(1, 10**12), n)))
        perms = []
        for _ in range(random_perm_count):
            perm = list(range(n))
            rng.shuffle(perm)
            perms.append(tuple(perm))
        ratio, perm = check_metric(values, perms)
        counters["metric_sets"] += 1
        counters["metric_permutations"] += len(perms)
        counters["metric_triangles"] += n ** 3
        if ratio > best_metric[0]:
            best_metric = (ratio, values, perm)
        if n not in metric_max_by_card or ratio > metric_max_by_card[n][0]:
            metric_max_by_card[n] = (ratio, values, perm)

    return {
        "mode": "quick" if quick else "full",
        "seed": 12620260902,
        "status": "PASS",
        "counters": counters,
        "minimum_weighted_padic_margin": min_weighted_margin,
        "minimum_heavy_margin_numerator_over_16": min_heavy_margin,
        "nontrivial_heavy_equality_witness": nontrivial_heavy_equality_witness,
        "largest_observed_metric_ratio": best_metric[0],
        "largest_metric_ratio_values": best_metric[1],
        "largest_metric_ratio_permutation": best_metric[2],
        "largest_metric_ratio_by_card": {
            str(n): {"ratio": item[0], "values": item[1], "permutation": item[2]}
            for n, item in sorted(metric_max_by_card.items())
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true", help="run the smaller CI-style suite")
    args = parser.parse_args()
    print(json.dumps(run(args.quick), indent=2))


if __name__ == "__main__":
    main()
