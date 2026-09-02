# Erdos 126 square-root proof: Lean continuation

These files are a standalone continuation of
`FormalConjectures/ErdosProblems/126.lean`.  The official source file is not
modified.  The checked final finite theorem is

```lean
theorem finite_quadratic_prime_support_bound
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 1600 * (addPrimeSupport A).card ^ 2
```

and `Erdos126Main.lean` proves the right-hand side of the official conjecture
from this theorem.

## Modules

- `Erdos126Support.lean`: unordered prime support and equivalence with the
  official ordered `offDiag` product.
- `Erdos126Normalized.lean`: pairwise gcd/2-adic normalization.
- `Erdos126Padic.lean`: maximum-score simultaneous matching, the complete
  odd/2-adic residue analysis, a direct unmatched-edge injection, and the
  threshold/weighted one-set matching theorems.
- `Erdos126Bias.lean`: exact `1/8` component moment and finite truncation.
- `Erdos126BiasedSample.lean`: a concrete finite product sample with the exact
  `5/16` and `3/16` pair moments and a coupled Bernoulli-`1/4` thin subset.
- `Erdos126BiasGlobal.lean`: sums the `1/8` slack over disjoint paired
  components and proves the global `3/16` retained-edge-mass bound.
- `Erdos126GoodEvent.lean`: exact thin-set variance, the `12/k` bad-density
  bound, and good-event restriction losses for edge mass and slack.
- `Erdos126RealGoodEvent.lean`: real-valued good-event bounds for logarithmic
  weights.
- `Erdos126HeavyPrimeBias.lean`: the canonical-side arithmetic-to-probability
  bridge giving expected selected p-adic slack at least `1/8` of the full
  normalized p-difference valuation mass.
- `Erdos126SideLabel.lean`: one canonical Bool label whose global flip
  simultaneously reverses every positive normalized sum threshold.
- `Erdos126Metric.lean`: one-part and bipartite metric matching bounds.
- `Erdos126MetricBridge.lean`: the arithmetic normalized-sum/log comparison
  and the abstract constant-`6/N` matching-cost theorem.
- `Erdos126LayerCake.lean`: generic threshold-cardinality to weighted-sum
  wrappers.
- `Erdos126ResiduePartition.lean`: an alternative checked component-summation
  proof of the local threshold count.
- `Erdos126Factorization.lean`: normalized-sum prime support, logarithmic
  p-adic factorization, and interchange of finite edge/prime sums.
- `Erdos126Potentials.lean`: the global `A`, `B`, `B_p`, `B_P` potentials,
  their nonnegativity comparisons, and `A = X + Y + Z` decomposition.
- `Erdos126AmbientIdentity.lean`: the logged identity over the original
  ambient prime support after sampling.
- `Erdos126SelectedMatching.lean`: restriction and re-optimization of a full
  p-adic involution on a selected subset.
- `Erdos126SelectionBridge.lean`: exact conversion from selected attached
  subtypes to finsets of natural numbers.
- `Erdos126HeavySelectionBridge.lean`: equality between probabilistic and
  selected-set heavy-prime slacks.
- `Erdos126HeavyGood.lean`: the heavy-prime gain on the good-size event.
- `Erdos126PotentialSelection.lean`: retention of the non-heavy `A-B_P`
  potential.
- `Erdos126MetricSum.lean`: the summed `6/|T|` matching-cost bound.
- `Erdos126FiniteTransfer.lean`: `n ≤ 1600 r^2` implies
  `Nat.sqrt n / 40 ≤ r` above the finite exceptional range.
- `Erdos126Asymptotic.lean`: square-root growth dominates `Real.log`.
- `Erdos126Numerical.lean`: the final expectation sandwich implies
  `k ≤ 1536 r^2`, hence the advertised safe constant `1600`.
- `Erdos126Bridge.lean`: checked transfer from the finite quadratic estimate
  to the official asymptotic statement.
- `Erdos126ZeroRemoval.lean`: support monotonicity and transfer from positive
  sets to the official natural-number formulation.
- `Erdos126Integration.lean`: the complete expectation sandwich,
  `k ≤ 1536 r²` for positive sets, and `k ≤ 1600 r²` after zero removal.
- `Erdos126Main.lean`: final integration with the official statement.
- `Erdos126BipartiteExploration.lean`: a separate unfinished exploratory
  `A+B` file; it is not imported by the `A+A` proof.

## Checked status

The complete `A+A` dependency chain compiles without `sorry`, `admit`,
`native_decide`, or custom axioms. `#print axioms` for both
`finite_quadratic_prime_support_bound` and the final asymptotic theorem reports
only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The official source file is intentionally unchanged: its `answer(sorry)`
placeholder encodes the yes/no answer. The continuation proves the entire
right-hand side of that equivalence. The separate exploratory `A+B` file has
two stated admits and is excluded from the proof chain and source archive.

## Local compilation

The new root modules are outside the repository's declared library glob, so add
the current directory to `LEAN_PATH` when compiling imports between them:

```bash
lake env bash -c 'LEAN_PATH=$LEAN_PATH:. lean Erdos126Bridge.lean'
lake env bash -c 'LEAN_PATH=$LEAN_PATH:. lean Erdos126Main.lean'
```

The supplied source targets Mathlib/Lean `v4.33.1`, matching the repository at
the time of preparation.
