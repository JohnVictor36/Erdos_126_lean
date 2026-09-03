import Erdos126Bridge
import Erdos126SimplifiedGlobal

/-!
# A continuation of the formal statement of Erdos problem 126

This file is the integration point for the deterministic square-root argument.
All imported auxiliary modules are kept separate from the official problem
statement. `Erdos126SimplifiedGlobal` proves the finite quadratic estimate, and
`erdos_126_rhs_of_finite_quadratic_bound` transfers it to the right-hand side
of the official conjecture.

For finsets of naturals, the hypothesis `2 < A.card` is necessary: the set
`{0, 1}` has two elements but no prime divides its only unordered pair sum.
This finite exception has no effect on the asymptotic conclusion.
-/

open Filter

namespace Erdos126

/-- The finite square-root estimate assembled from normalized p-adic
matchings, deterministic residue splitting, and the valuation metric.

The deterministic argument gives coefficient `12` for positive sets. Erasing
a possible zero gives coefficient `13` for arbitrary natural-number finsets.
-/
theorem finite_quadratic_prime_support_bound
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 13 * (addPrimeSupport A).card ^ 2 := by
  exact finite_quadratic_prime_support_bound_deterministic A hcard

/-- The asymptotic assertion on the right-hand side of the official
`erdos_126` statement follows with no further number-theoretic input. -/
theorem erdos_126_rhs_of_finite_quadratic_bound :
    ∀ f, IsMaximalAddFactorsCard f →
      Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  intro f hf
  apply tendsto_maximalAddFactorsCard_of_card_le_const_mul_support_sq
    f 13 (by norm_num) hf
  intro n A hA hn
  simpa [hA] using finite_quadratic_prime_support_bound A (hA.symm ▸ hn)

end Erdos126
