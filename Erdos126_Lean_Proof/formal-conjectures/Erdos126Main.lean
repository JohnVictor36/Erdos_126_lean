import Erdos126Bias
import Erdos126BiasedSample
import Erdos126BiasGlobal
import Erdos126Bridge
import Erdos126FiniteTransfer
import Erdos126Factorization
import Erdos126GoodEvent
import Erdos126HeavyPrimeBias
import Erdos126Integration
import Erdos126LayerCake
import Erdos126Metric
import Erdos126MetricBridge
import Erdos126Normalized
import Erdos126Numerical
import Erdos126Padic
import Erdos126Potentials
import Erdos126ResiduePartition
import Erdos126SideLabel
import Erdos126ZeroRemoval

/-!
# A continuation of the formal statement of Erdos problem 126

This file is the integration point for the square-root argument.  All imported
auxiliary modules are kept separate from the official problem statement.
`Erdos126Integration` proves the finite quadratic estimate, and
`erdos_126_rhs_of_finite_quadratic_bound` transfers it to the right-hand side
of the official conjecture.

For finsets of naturals, the hypothesis `2 < A.card` is necessary: the set
`{0, 1}` has two elements but no prime divides its only unordered pair sum.
This finite exception has no effect on the asymptotic conclusion.
-/

open Filter

namespace Erdos126

/-- The finite square-root estimate assembled from the normalized p-adic
matching, biased selection, and valuation-metric modules.

The paper argument gives the better constant `768` for positive sets.  The
constant `1600` leaves room to erase a possible zero and to absorb the small
cardinality cases in the official formulation over `Finset ℕ`.
-/
theorem finite_quadratic_prime_support_bound
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 1600 * (addPrimeSupport A).card ^ 2 := by
  exact finite_quadratic_prime_support_bound_integrated A hcard

/-- The asymptotic assertion on the right-hand side of the official
`erdos_126` statement follows with no further number-theoretic input. -/
theorem erdos_126_rhs_of_finite_quadratic_bound :
    ∀ f, IsMaximalAddFactorsCard f →
      Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  intro f hf
  apply tendsto_maximalAddFactorsCard_of_card_le_const_mul_support_sq
    f 1600 (by norm_num) hf
  intro n A hA hn
  simpa [hA] using finite_quadratic_prime_support_bound A (hA.symm ▸ hn)

end Erdos126
