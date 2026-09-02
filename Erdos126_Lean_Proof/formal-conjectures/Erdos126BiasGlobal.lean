import Erdos126Bias
import Erdos126BiasedSample

/-!
# Global finite averaging for the biased component construction

This file sums the exact local pair marginals of `Erdos126BiasedSample` over
paired components.  A component carries an explicit maximum cross-matching;
this is the certificate for the `min (#L) (#R)` term in the component moment.
No measure theory is used.
-/

open scoped BigOperators

namespace Erdos126.BiasGlobal

open Erdos126.Bias Erdos126.BiasedSample

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A pair of opposite-side vertex classes, together with a certified maximum
cross-matching.  Endpoint injectivity records that `matching` really is a
matching, although only its cardinality is needed for the expectation identity. -/
structure PairedComponent (side : V → Bool) where
  left : Finset V
  right : Finset V
  disjoint : Disjoint left right
  left_side : ∀ v ∈ left, side v = false
  right_side : ∀ v ∈ right, side v = true
  matching : Finset (V × V)
  matching_mem : ∀ e ∈ matching, e.1 ∈ left ∧ e.2 ∈ right
  matching_card : matching.card = min left.card right.card
  matching_fst_injective : Set.InjOn Prod.fst (matching : Set (V × V))
  matching_snd_injective : Set.InjOn Prod.snd (matching : Set (V × V))

/-- Indicator that both endpoints of an ordered pair are retained. -/
def pairIndicator (side : V → Bool) (omega : SystemSample V) (e : V × V) : ℚ :=
  retainedIndicator omega.orientation (side e.1) (omega.label e.1) *
    retainedIndicator omega.orientation (side e.2) (omega.label e.2)

/-- The unordered pairs internal to a finite vertex class, represented by the
ambient linear order. -/
def strictPairs (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun e => e.1 < e.2

/-- Sum of retained-pair indicators over an edge finset. -/
def retainedEdgeMass (side : V → Bool) (E : Finset (V × V))
    (omega : SystemSample V) : ℚ :=
  ∑ e ∈ E, pairIndicator side omega e

/-- The local slack: retained internal pairs, minus all retained cross pairs,
plus the retained edges of a fixed maximum matching. -/
def componentSlack (side : V → Bool) (C : PairedComponent side)
    (omega : SystemSample V) : ℚ :=
  retainedEdgeMass side (strictPairs C.left) omega +
      retainedEdgeMass side (strictPairs C.right) omega -
    retainedEdgeMass side (C.left ×ˢ C.right) omega +
    retainedEdgeMass side C.matching omega

/-- Original internal-pair mass of one component. -/
def componentWithinMass (side : V → Bool) (C : PairedComponent side) : ℚ :=
  chooseTwoQ C.left.card + chooseTwoQ C.right.card

lemma expect_retainedEdgeMass (side : V → Bool) (E : Finset (V × V)) :
    (𝔼 omega : SystemSample V, retainedEdgeMass side E omega) =
      ∑ e ∈ E, 𝔼 omega : SystemSample V, pairIndicator side omega e := by
  simp only [retainedEdgeMass, Finset.expect_sum_comm]

lemma expect_internal_left (side : V → Bool) (C : PairedComponent side) :
    (𝔼 omega : SystemSample V,
      retainedEdgeMass side (strictPairs C.left) omega) =
      5 / 16 * chooseTwoQ C.left.card := by
  rw [expect_retainedEdgeMass]
  calc
    (∑ e ∈ strictPairs C.left,
        𝔼 omega : SystemSample V, pairIndicator side omega e) =
        ∑ _e ∈ strictPairs C.left, (5 / 16 : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := (Finset.mem_filter.mp he)
      have hmem := Finset.mem_product.mp he'.1
      have hne : e.1 ≠ e.2 := ne_of_lt he'.2
      unfold pairIndicator
      exact expect_system_sameSide_pair side hne
        ((C.left_side e.1 hmem.1).trans (C.left_side e.2 hmem.2).symm)
    _ = ((strictPairs C.left).card : ℚ) * (5 / 16 : ℚ) := by simp
    _ = 5 / 16 * chooseTwoQ C.left.card := by
      rw [strictPairs, Finset.card_product_filter_lt, chooseTwoQ_natCast]
      ring

lemma expect_internal_right (side : V → Bool) (C : PairedComponent side) :
    (𝔼 omega : SystemSample V,
      retainedEdgeMass side (strictPairs C.right) omega) =
      5 / 16 * chooseTwoQ C.right.card := by
  rw [expect_retainedEdgeMass]
  calc
    (∑ e ∈ strictPairs C.right,
        𝔼 omega : SystemSample V, pairIndicator side omega e) =
        ∑ _e ∈ strictPairs C.right, (5 / 16 : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := (Finset.mem_filter.mp he)
      have hmem := Finset.mem_product.mp he'.1
      have hne : e.1 ≠ e.2 := ne_of_lt he'.2
      unfold pairIndicator
      exact expect_system_sameSide_pair side hne
        ((C.right_side e.1 hmem.1).trans (C.right_side e.2 hmem.2).symm)
    _ = ((strictPairs C.right).card : ℚ) * (5 / 16 : ℚ) := by simp
    _ = 5 / 16 * chooseTwoQ C.right.card := by
      rw [strictPairs, Finset.card_product_filter_lt, chooseTwoQ_natCast]
      ring

lemma expect_cross (side : V → Bool) (C : PairedComponent side) :
    (𝔼 omega : SystemSample V,
      retainedEdgeMass side (C.left ×ˢ C.right) omega) =
      3 / 16 * (C.left.card : ℚ) * C.right.card := by
  rw [expect_retainedEdgeMass]
  calc
    (∑ e ∈ C.left ×ˢ C.right,
        𝔼 omega : SystemSample V, pairIndicator side omega e) =
        ∑ _e ∈ C.left ×ˢ C.right, (3 / 16 : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      have hmem := Finset.mem_product.mp he
      have hne : e.1 ≠ e.2 := by
        intro h
        apply Finset.disjoint_left.mp C.disjoint hmem.1
        simpa [h] using hmem.2
      unfold pairIndicator
      apply expect_system_oppositeSide_pair side hne
      rw [C.left_side e.1 hmem.1, C.right_side e.2 hmem.2]
      rfl
    _ = (((C.left ×ˢ C.right).card : ℕ) : ℚ) * (3 / 16 : ℚ) := by simp
    _ = 3 / 16 * (C.left.card : ℚ) * C.right.card := by
      rw [Finset.card_product, Nat.cast_mul]
      ring

lemma expect_matching (side : V → Bool) (C : PairedComponent side) :
    (𝔼 omega : SystemSample V,
      retainedEdgeMass side C.matching omega) =
      3 / 16 * ((min C.left.card C.right.card : ℕ) : ℚ) := by
  rw [expect_retainedEdgeMass]
  calc
    (∑ e ∈ C.matching,
        𝔼 omega : SystemSample V, pairIndicator side omega e) =
        ∑ _e ∈ C.matching, (3 / 16 : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      have hmem := C.matching_mem e he
      have hne : e.1 ≠ e.2 := by
        intro h
        apply Finset.disjoint_left.mp C.disjoint hmem.1
        simpa [h] using hmem.2
      unfold pairIndicator
      apply expect_system_oppositeSide_pair side hne
      rw [C.left_side e.1 hmem.1, C.right_side e.2 hmem.2]
      rfl
    _ = (C.matching.card : ℚ) * (3 / 16 : ℚ) := by simp
    _ = 3 / 16 * ((min C.left.card C.right.card : ℕ) : ℚ) := by
      rw [C.matching_card]
      ring

/-- Expected slack of one component is at least one eighth of its original
within-side pair mass. -/
theorem one_eighth_componentWithinMass_le_expect_componentSlack
    (side : V → Bool) (C : PairedComponent side) :
    1 / 8 * componentWithinMass side C ≤
      𝔼 omega : SystemSample V, componentSlack side C omega := by
  simp only [componentSlack]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    Finset.expect_add_distrib, expect_internal_left, expect_internal_right,
    expect_cross, expect_matching, componentWithinMass]
  nlinarith [one_eighth_le_component_moment C.left.card C.right.card]

/-- Summed internal-pair mass of a finite component family. -/
def totalWithinMass {I : Type*} (indices : Finset I) (side : V → Bool)
    (C : I → PairedComponent side) : ℚ :=
  ∑ i ∈ indices, componentWithinMass side (C i)

/-- Summed random slack of a finite component family. -/
def totalSlack {I : Type*} (indices : Finset I) (side : V → Bool)
    (C : I → PairedComponent side) (omega : SystemSample V) : ℚ :=
  ∑ i ∈ indices, componentSlack side (C i) omega

/-- Global component inequality.  Disjointness is part of the interface needed
by applications; the expectation argument itself is linear and therefore does
not need to spend this hypothesis. -/
theorem one_eighth_totalWithinMass_le_expect_totalSlack
    {I : Type*} [DecidableEq I] (indices : Finset I) (side : V → Bool)
    (C : I → PairedComponent side)
    (_hdisjoint : Set.PairwiseDisjoint (indices : Set I)
      fun i => (C i).left ∪ (C i).right) :
    1 / 8 * totalWithinMass indices side C ≤
      𝔼 omega : SystemSample V, totalSlack indices side C omega := by
  simp only [totalWithinMass, totalSlack]
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    one_eighth_componentWithinMass_le_expect_componentSlack side (C i)

/-- Every distinct pair is retained with probability at least `3/16`. -/
lemma three_sixteenths_le_expect_pairIndicator
    (side : V → Bool) {u v : V} (huv : u ≠ v) :
    (3 / 16 : ℚ) ≤ 𝔼 omega : SystemSample V, pairIndicator side omega (u, v) := by
  by_cases hsame : side u = side v
  · unfold pairIndicator
    rw [expect_system_sameSide_pair side huv hsame]
    norm_num
  · have hopp : side v = !(side u) := by
      cases hu : side u <;> cases hv : side v <;> simp_all
    unfold pairIndicator
    rw [expect_system_oppositeSide_pair side huv hopp]

/-- A nonnegative weighting of all ordered off-diagonal edges retains at least
`3/16` of its total weight in expectation. -/
theorem three_sixteenths_weight_le_expect_retained_offDiag
    (side : V → Bool) (weight : V × V → ℚ) (hweight : ∀ e, 0 ≤ weight e) :
    3 / 16 * (∑ e ∈ (Finset.univ : Finset V).offDiag, weight e) ≤
      𝔼 omega : SystemSample V,
        ∑ e ∈ (Finset.univ : Finset V).offDiag,
          weight e * pairIndicator side omega e := by
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
  calc
    3 / 16 * weight e = weight e * (3 / 16) := by ring
    _ ≤ weight e * (𝔼 omega : SystemSample V, pairIndicator side omega e) :=
      mul_le_mul_of_nonneg_left
        (three_sixteenths_le_expect_pairIndicator side hne) (hweight e)
    _ = 𝔼 omega : SystemSample V, weight e * pairIndicator side omega e :=
      Finset.mul_expect _ _ _

end Erdos126.BiasGlobal
