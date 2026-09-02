import Erdos126GoodEvent

/-!
# Real-valued good-event estimates

`Erdos126GoodEvent` proves the finite counting estimate over `ℚ`.  The global
logarithmic potentials have real weights, so this file supplies the identical
restriction lemma over `ℝ`.  The random indicator is still the same exact
zero-one rational variable, merely coerced to the reals.
-/

open scoped BigOperators

namespace Erdos126.RealGoodEvent

open BiasedSample BiasGlobal GoodEvent

variable {V : Type*} [Fintype V] [LinearOrder V]

instance : Nonempty (SystemSample V) :=
  ⟨⟨false, fun _ => 0⟩⟩

def realPairIndicator (side : V → Bool) (omega : SystemSample V)
    (e : V × V) : ℝ :=
  (pairIndicator side omega e : ℚ)

lemma ratCast_expect {Omega : Type*} [Fintype Omega] (F : Omega → ℚ) :
    (((𝔼 omega : Omega, F omega) : ℚ) : ℝ) =
      𝔼 omega : Omega, (F omega : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  push_cast
  rfl

lemma realPairIndicator_nonneg
    (side : V → Bool) (omega : SystemSample V) (e : V × V) :
    0 ≤ realPairIndicator side omega e := by
  unfold realPairIndicator
  exact_mod_cast GoodEvent.pairIndicator_nonneg side omega e

lemma realPairIndicator_le_one
    (side : V → Bool) (omega : SystemSample V) (e : V × V) :
    realPairIndicator side omega e ≤ 1 := by
  unfold realPairIndicator
  exact_mod_cast GoodEvent.pairIndicator_le_one side omega e

lemma three_sixteenths_le_expect_realPairIndicator
    (side : V → Bool) {u v : V} (huv : u ≠ v) :
    (3 / 16 : ℝ) ≤
      𝔼 omega : SystemSample V, realPairIndicator side omega (u, v) := by
  have hq := three_sixteenths_le_expect_pairIndicator side huv
  change (3 / 16 : ℝ) ≤
    𝔼 omega : SystemSample V,
      ((pairIndicator side omega (u, v) : ℚ) : ℝ)
  rw [← ratCast_expect]
  have hc : (((3 / 16 : ℚ) : ℝ) ≤
      (((𝔼 omega : SystemSample V,
        pairIndicator side omega (u, v)) : ℚ) : ℝ)) :=
    (Rat.cast_le (K := ℝ)).mpr hq
  norm_num at hc ⊢
  exact hc

/-- A nonnegative real weighting of all ordered off-diagonal edges retains at
least `3/16` of its total weight in expectation. -/
theorem three_sixteenths_weight_le_expect_real_offDiag
    (side : V → Bool) (weight : V × V → ℝ) (hweight : ∀ e, 0 ≤ weight e) :
    3 / 16 * (∑ e ∈ (Finset.univ : Finset V).offDiag, weight e) ≤
      𝔼 omega : SystemSample V,
        ∑ e ∈ (Finset.univ : Finset V).offDiag,
          weight e * realPairIndicator side omega e := by
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
  calc
    3 / 16 * weight e = weight e * (3 / 16) := by ring
    _ ≤ weight e *
        (𝔼 omega : SystemSample V, realPairIndicator side omega e) :=
      mul_le_mul_of_nonneg_left
        (three_sixteenths_le_expect_realPairIndicator side hne) (hweight e)
    _ = 𝔼 omega : SystemSample V,
        weight e * realPairIndicator side omega e :=
      Finset.mul_expect _ _ _

theorem bad_selected_real_density_le_twelve_div
    (side : V → Bool) (k : ℕ) (hk : 0 < k) (hcard : Fintype.card V = k) :
    (((Finset.univ.filter fun omega : SystemSample V =>
        ¬ Good side k omega).card : ℕ) : ℝ) /
        Fintype.card (SystemSample V) ≤ 12 / (k : ℝ) := by
  have hq := GoodEvent.bad_selected_density_le_twelve_div side k hk hcard
  have hc := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at hc
  exact hc

/-- Real analogue of the generic bad-event loss estimate. -/
theorem expect_sub_badLoss_le_expect_restrict_good
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (F : Omega → ℝ) (GoodEvent : Omega → Prop) [DecidablePred GoodEvent]
    (B delta : ℝ) (hB : 0 ≤ B) (hFle : ∀ omega, F omega ≤ B)
    (hbad :
      (((Finset.univ.filter fun omega : Omega => ¬ GoodEvent omega).card : ℕ) : ℝ) /
        Fintype.card Omega ≤ delta) :
    (𝔼 omega, F omega) - delta * B ≤
      𝔼 omega, if GoodEvent omega then F omega else 0 := by
  let bad : Finset Omega := Finset.univ.filter fun omega => ¬ GoodEvent omega
  have hbadExpect :
      (𝔼 omega, if ¬ GoodEvent omega then F omega else 0) ≤ delta * B := by
    rw [Fintype.expect_eq_sum_div_card]
    calc
      (∑ omega : Omega, if ¬ GoodEvent omega then F omega else 0) /
          Fintype.card Omega = (∑ omega ∈ bad, F omega) /
            Fintype.card Omega := by
        congr 1
        rw [Finset.sum_filter]
      _ ≤ (bad.card * B) / Fintype.card Omega := by
        gcongr
        simpa using Finset.sum_le_card_nsmul bad F B fun omega _ => hFle omega
      _ = ((bad.card : ℝ) / Fintype.card Omega) * B := by ring
      _ ≤ delta * B := mul_le_mul_of_nonneg_right hbad hB
  have hsplit :
      (𝔼 omega, F omega) =
        (𝔼 omega, if GoodEvent omega then F omega else 0) +
          𝔼 omega, if ¬ GoodEvent omega then F omega else 0 := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro omega _
    by_cases h : GoodEvent omega <;> simp [h]
  rw [hsplit]
  linarith

/-- On the selected-size good event, a nonnegative real off-diagonal edge
mass retains the same `(3/16 - 12/k)` fraction as in the rational lemma. -/
theorem good_restricted_real_edgeMass_ge
    (side : V → Bool) (k : ℕ) (hk : 0 < k) (hcard : Fintype.card V = k)
    (weight : V × V → ℝ) (hweight : ∀ e, 0 ≤ weight e) :
    (3 / 16 - 12 / (k : ℝ)) *
        (∑ e ∈ (Finset.univ : Finset V).offDiag, weight e) ≤
      𝔼 omega : SystemSample V,
        if Good side k omega then
          ∑ e ∈ (Finset.univ : Finset V).offDiag,
            weight e * realPairIndicator side omega e
        else 0 := by
  let B : ℝ := ∑ e ∈ (Finset.univ : Finset V).offDiag, weight e
  let F : SystemSample V → ℝ := fun omega =>
    ∑ e ∈ (Finset.univ : Finset V).offDiag,
      weight e * realPairIndicator side omega e
  have hB : 0 ≤ B := Finset.sum_nonneg fun e _ => hweight e
  have hFnonneg : ∀ omega, 0 ≤ F omega := by
    intro omega
    exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (hweight e) (realPairIndicator_nonneg side omega e)
  have hFle : ∀ omega, F omega ≤ B := by
    intro omega
    apply Finset.sum_le_sum
    intro e _
    simpa only [F, B, mul_one] using mul_le_mul_of_nonneg_left
      (realPairIndicator_le_one side omega e) (hweight e)
  have hfull : 3 / 16 * B ≤ 𝔼 omega, F omega := by
    simpa only [F, B] using
      three_sixteenths_weight_le_expect_real_offDiag side weight hweight
  have hrestrict := expect_sub_badLoss_le_expect_restrict_good
    F (Good side k) B (12 / (k : ℝ)) hB hFle
    (bad_selected_real_density_le_twelve_div side k hk hcard)
  dsimp only [F] at hrestrict ⊢
  change (3 / 16 - 12 / (k : ℝ)) * B ≤ _
  nlinarith

end Erdos126.RealGoodEvent
