import Erdos126Potentials
import Erdos126HeavyPrimeBias
import Erdos126GoodEvent
import Erdos126MetricBridge
import Erdos126Numerical

/-!
# Global integration interface for Erdős problem 126

The checked modules now discharge the arithmetic normalization, the one-prime
biased expectation, the good-size tail bound, the abstract metric estimate,
and the final numerical cancellation.  This file records the exact remaining
integration statement and proves that it implies the desired finite bound.

The unconditional theorem is not yet derivable from the current interfaces.
In particular, the following glue is still absent:

* conversion of `BiasedSample.selectedSet`, a finset of the subtype `T`, to a
  natural-number finset on which `Potentials.logged_involution_identity` can be
  applied;
* restriction of the heavy-prime involution to that selected subtype, with
  equality between its cost and `selectedNormalizedMatchingMass`;
* a real-valued good-event edge-mass lemma for the logarithmic `X` and `Y`
  weights, plus the cast from the rational heavy-prime slack expectation;
* the pointwise sum, over all support primes, of the metric bounds for the
  selected-set involutions.

These four items are packaged below as one expectation sandwich.  No
number-theoretic assertion is assumed in the final cancellation itself.
-/

namespace Erdos126

open scoped BigOperators

noncomputable section

/-- A positive set with at least two elements has a nonempty additive prime
support. -/
theorem addPrimeSupport_nonempty_of_two_le
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    (addPrimeSupport T).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  have habSumPos : 0 < a + b := Nat.add_pos_left (hT a ha) b
  have habSumNeOne : a + b ≠ 1 := by
    have hap := hT a ha
    have hbp := hT b hb
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd habSumNeOne
  have hpSum : p ∈ (a + b).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, habSumPos.ne'⟩
  exact ⟨p, primeFactors_sum_subset_addPrimeSupport ha hb hab hpSum⟩

/-- The ordered normalized-sum potential is strictly positive once there is
an off-diagonal edge. -/
theorem AweightOrdered_pos
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    0 < AweightOrdered T := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  rw [AweightOrdered]
  apply Finset.sum_pos'
  · intro e he
    have he' := Finset.mem_offDiag.mp he
    apply Real.log_nonneg
    have htwo := Normalized.two_le_normalizedSum
      (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2
    exact_mod_cast (show 1 ≤ Normalized.normalizedSum e.1 e.2 by omega)
  · refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, ?_⟩
    apply Real.log_pos
    have htwo := Normalized.two_le_normalizedSum
      (hT a ha) (hT b hb) hab
    exact_mod_cast htwo

/-- Finite averaging supplies the heavy prime before any random subset is
chosen.  This quantifier order is the one required by `HeavyPrimeBias`. -/
theorem exists_BpOrdered_ge_average
    (P : Finset ℕ) (T : Finset ℕ) (hP : P.Nonempty) :
    ∃ p ∈ P,
      BPOrdered P T / (P.card : ℝ) ≤ BpOrdered p T := by
  obtain ⟨p, hp, hpmax⟩ :=
    Finset.exists_max_image P (fun q => BpOrdered q T) hP
  refine ⟨p, hp, ?_⟩
  have hsum : BPOrdered P T ≤ (P.card : ℝ) * BpOrdered p T := by
    rw [BPOrdered]
    simpa using Finset.sum_le_card_nsmul P (fun q => BpOrdered q T)
      (BpOrdered p T) hpmax
  have hcard : (0 : ℝ) < P.card := by
    exact_mod_cast Finset.card_pos.mpr hP
  apply (div_le_iff₀ hcard).mpr
  simpa [mul_comm] using hsum

/-- The exact large-set statement still needed from the probabilistic and
matching interfaces.

`average` is intended to be the good-event expectation of the logged matching
identity on the biased subset. -/
def GlobalExpectationSandwich (T : Finset ℕ) : Prop :=
  ∃ average : ℝ,
    (1 / (16 * ((addPrimeSupport T).card : ℝ))) * AweightOrdered T ≤ average ∧
      average ≤
        (96 * ((addPrimeSupport T).card : ℝ) / (T.card : ℝ)) * AweightOrdered T

/-- Once the expectation sandwich is available, the large-cardinality finite
bound follows from the compiled numerical lemma. -/
theorem card_le_1600_support_sq_of_expectationSandwich
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (hS : GlobalExpectationSandwich T) :
    T.card ≤ 1600 * (addPrimeSupport T).card ^ 2 := by
  obtain ⟨average, hlower, hupper⟩ := hS
  have hP := addPrimeSupport_nonempty_of_two_le T hT hcard
  have hr : 0 < (addPrimeSupport T).card := Finset.card_pos.mpr hP
  have hk : 0 < T.card := lt_of_lt_of_le Nat.zero_lt_two hcard
  exact Numerical.card_le_1600_mul_sq
    (AweightOrdered T) average T.card (addPrimeSupport T).card
    (AweightOrdered_pos T hT hcard) hk hr hlower hupper

/-- Exact-coefficient version retained for the final zero-removal step. -/
theorem card_le_1536_support_sq_of_expectationSandwich
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (hS : GlobalExpectationSandwich T) :
    T.card ≤ 1536 * (addPrimeSupport T).card ^ 2 := by
  obtain ⟨average, hlower, hupper⟩ := hS
  have hP := addPrimeSupport_nonempty_of_two_le T hT hcard
  have hr : 0 < (addPrimeSupport T).card := Finset.card_pos.mpr hP
  have hk : 0 < T.card := lt_of_lt_of_le Nat.zero_lt_two hcard
  exact Numerical.card_le_1536_mul_sq
    (AweightOrdered T) average T.card (addPrimeSupport T).card
    (AweightOrdered_pos T hT hcard) hk hr hlower hupper

/-- The bounded range `card T ≤ 192` only uses nonemptiness of the prime
support. -/
theorem small_positive_card_le_1600_support_sq
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (hcard : 2 ≤ T.card) (hsmall : T.card ≤ 192) :
    T.card ≤ 1600 * (addPrimeSupport T).card ^ 2 := by
  have hP := addPrimeSupport_nonempty_of_two_le T hT hcard
  exact Numerical.small_card_le_1600_mul_sq T.card
    (addPrimeSupport T).card hsmall (Finset.one_le_card.mpr hP)

theorem small_positive_card_le_1536_support_sq
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (hcard : 2 ≤ T.card) (hsmall : T.card ≤ 192) :
    T.card ≤ 1536 * (addPrimeSupport T).card ^ 2 := by
  have hP := addPrimeSupport_nonempty_of_two_le T hT hcard
  have hr : 1 ≤ (addPrimeSupport T).card := Finset.one_le_card.mpr hP
  have hrsq : 1 ≤ (addPrimeSupport T).card ^ 2 := one_le_pow₀ hr
  calc
    T.card ≤ 192 := hsmall
    _ ≤ 1536 := by norm_num
    _ = 1536 * 1 := by ring
    _ ≤ 1536 * (addPrimeSupport T).card ^ 2 := Nat.mul_le_mul_left 1536 hrsq

/-- Exact proposition which the remaining integration must establish. -/
def GlobalExpectationGlue : Prop :=
  ∀ (T : Finset ℕ), (∀ a ∈ T, 0 < a) →
    192 < T.card → GlobalExpectationSandwich T

/-- Conditional final theorem: this has exactly the target statement for
positive finsets and isolates the sole remaining global glue. -/
theorem positive_card_le_1600_support_sq_of_globalExpectationGlue
    (hglue : GlobalExpectationGlue)
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 < T.card) :
    T.card ≤ 1600 * (addPrimeSupport T).card ^ 2 := by
  have hcard2 : 2 ≤ T.card := hcard.le
  by_cases hsmall : T.card ≤ 192
  · exact small_positive_card_le_1600_support_sq T hT hcard2 hsmall
  · exact card_le_1600_support_sq_of_expectationSandwich T hT hcard2
      (hglue T hT (Nat.lt_of_not_ge hsmall))

theorem positive_card_le_1536_support_sq_of_globalExpectationGlue
    (hglue : GlobalExpectationGlue)
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 < T.card) :
    T.card ≤ 1536 * (addPrimeSupport T).card ^ 2 := by
  have hcard2 : 2 ≤ T.card := hcard.le
  by_cases hsmall : T.card ≤ 192
  · exact small_positive_card_le_1536_support_sq T hT hcard2 hsmall
  · exact card_le_1536_support_sq_of_expectationSandwich T hT hcard2
      (hglue T hT (Nat.lt_of_not_ge hsmall))

end

end Erdos126
