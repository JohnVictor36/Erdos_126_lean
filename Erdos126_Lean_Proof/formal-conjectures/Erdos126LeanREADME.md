# Erdos 126 square-root proof: Lean continuation

These files are a standalone continuation of
`FormalConjectures/ErdosProblems/126.lean`.  The official source file is not
modified.  The checked final finite theorem is

```lean
theorem finite_quadratic_prime_support_bound
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 13 * (addPrimeSupport A).card ^ 2
```

and `Erdos126Main.lean` proves the right-hand side of the official conjecture
from this theorem.

## Modules

- `Erdos126Support.lean`: unordered prime support and equivalence with the
  official ordered `offDiag` product.
- `Erdos126Normalized.lean`: pairwise gcd/2-adic normalization.
- `Erdos126Padic.lean`: simultaneous normalized p-adic matchings and their
  nonnegative slack, for odd primes and for `p = 2`.
- `Erdos126SideLabel.lean`: one canonical Bool label whose global flip
  simultaneously reverses every positive normalized sum threshold.
- `Erdos126DeterministicSplit.lean`: the two canonical sides, exact splitting
  of `B_p`, and gluing of two side involutions into one ambient involution.
- `Erdos126Metric.lean`: one-part and bipartite metric matching bounds.
- `Erdos126MetricBridge.lean`: the arithmetic normalized-sum/log comparison
  and the abstract constant-`6/N` matching-cost theorem.
- `Erdos126Factorization.lean`: normalized-sum prime support, logarithmic
  p-adic factorization, and interchange of finite edge/prime sums.
- `Erdos126Potentials.lean`: the global `A`, `B`, `B_p`, `B_P` potentials,
  and their nonnegativity comparisons.
- `Erdos126AmbientIdentity.lean`: the logged matching identity over an ambient
  prime support.
- `Erdos126MetricSum.lean`: the summed `6/|T|` matching-cost bound.
- `Erdos126Asymptotic.lean`: square-root growth dominates `Real.log`.
- `Erdos126Bridge.lean`: checked transfer from the finite quadratic estimate
  to the official asymptotic statement.
- `Erdos126ZeroRemoval.lean`: support monotonicity and transfer from positive
  sets to the official natural-number formulation.
- `Erdos126SimplifiedGlobal.lean`: the deterministic cancellation
  `k ≤ 6r(r+1) ≤ 12r²` for positive sets and the coefficient-`13`
  zero-removal transfer.
- `Erdos126Main.lean`: final integration with the official statement.

## Checked status

The complete `A+A` dependency chain compiles without `sorry`, `admit`,
`native_decide`, or custom axioms. `#print axioms` for both
`finite_quadratic_prime_support_bound` and the final asymptotic theorem reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The official source file is intentionally unchanged: its `answer(sorry)`
placeholder encodes the yes/no answer. The continuation proves the entire
right-hand side of that equivalence. The former probabilistic selection,
Chernoff, and good-event modules are not part of the cleaned source archive.

## Local compilation

Copy the `.lean` files to the root of a clone of `formal-conjectures`. The new
root modules are outside the repository's declared library glob, so add the
current directory to `LEAN_PATH`:

```bash
lake exe cache get
lake env bash -c 'LEAN_PATH=$LEAN_PATH:. lean Erdos126Main.lean'
```

The supplied source targets Mathlib/Lean `v4.33.1`, matching the repository at
the time of preparation.
