import Erdos126SelectionBridge

/-!
# Retaining the non-heavy logarithmic potential on the good event
-/

namespace Erdos126

open scoped BigOperators
open BiasedSample BiasGlobal GoodEvent
open RealGoodEvent SelectionBridge

noncomputable section

def ambientGapWeight (P : Finset ℕ) (e : ℕ × ℕ) : ℝ :=
  Real.log (Normalized.normalizedSum e.1 e.2) -
    ∑ p ∈ P,
      (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) * Real.log p

theorem ambientGapWeight_nonneg
    (T P : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime)
    (e : T × T) (hne : e.1 ≠ e.2) :
    0 ≤ ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ)) := by
  have hdist := sum_padicValNat_log_le_log
    (Normalized.normalizedDist_pos
      (hT e.1 e.1.property) (hT e.2 e.2.property)
      (fun h => hne (Subtype.ext h))) P hprime
  have hlt :
      Real.log (Normalized.normalizedDist (e.1 : ℕ) (e.2 : ℕ)) <
        Real.log (Normalized.normalizedSum (e.1 : ℕ) (e.2 : ℕ)) := by
    have hD : 0 < (Normalized.normalizedDist (e.1 : ℕ) (e.2 : ℕ) : ℝ) := by
      exact_mod_cast Normalized.normalizedDist_pos
        (hT e.1 e.1.property) (hT e.2 e.2.property)
        (fun h => hne (Subtype.ext h))
    have hU : 0 < (Normalized.normalizedSum (e.1 : ℕ) (e.2 : ℕ) : ℝ) := by
      exact_mod_cast Normalized.normalizedSum_pos
        (hT e.1 e.1.property) (hT e.2 e.2.property)
    exact Real.strictMonoOn_log hD hU (by
      exact_mod_cast normalizedDist_lt_normalizedSum
        (hT e.1 e.1.property) (hT e.2 e.2.property)
        (fun h => hne (Subtype.ext h)))
  unfold ambientGapWeight
  linarith

theorem sum_ambientGapWeight_eq
    (T P : Finset ℕ) :
    (∑ e ∈ T.offDiag, ambientGapWeight P e) =
      AweightOrdered T - BPOrdered P T := by
  rw [AweightOrdered, BPOrdered]
  simp only [BpOrdered]
  calc
    _ = ∑ e ∈ T.offDiag,
        (Real.log (Normalized.normalizedSum e.1 e.2) -
          ∑ p ∈ P,
            (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
              Real.log p) := by rfl
    _ = (∑ e ∈ T.offDiag,
          Real.log (Normalized.normalizedSum e.1 e.2)) -
        ∑ e ∈ T.offDiag, ∑ p ∈ P,
          (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
            Real.log p := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ e ∈ T.offDiag,
          Real.log (Normalized.normalizedSum e.1 e.2)) -
        ∑ p ∈ P, ∑ e ∈ T.offDiag,
          (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
            Real.log p := by rw [Finset.sum_comm]

/-- The ordered normalized-sum potential is monotone under passage to a
subset of a positive finset. -/
theorem AweightOrdered_mono_of_subset
    {S T : Finset ℕ} (hST : S ⊆ T) (hT : ∀ a ∈ T, 0 < a) :
    AweightOrdered S ≤ AweightOrdered T := by
  rw [AweightOrdered, AweightOrdered]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    have he' := Finset.mem_offDiag.mp he
    exact Finset.mem_offDiag.mpr
      ⟨hST he'.1, hST he'.2.1, he'.2.2⟩
  · intro e heT heS
    have he' := Finset.mem_offDiag.mp heT
    apply Real.log_nonneg
    exact_mod_cast Normalized.normalizedSum_pos
      (hT e.1 he'.1) (hT e.2 he'.2.1)

theorem selected_gap_eq_indicator
    (T P : Finset ℕ) (side : T → Bool) (omega : SystemSample T) :
    AweightOrdered (selectedNat (selectedSet side omega)) -
        BPOrdered P (selectedNat (selectedSet side omega)) =
      ∑ e ∈ (Finset.univ : Finset T).offDiag,
        ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ)) *
          realPairIndicator side omega e := by
  rw [AweightOrdered_selectedSet, BPOrdered_selectedSet]
  calc
    _ = (∑ e ∈ (Finset.univ : Finset T).offDiag,
          Real.log (Normalized.normalizedSum e.1 e.2) *
            realPairIndicator side omega e) -
        ∑ e ∈ (Finset.univ : Finset T).offDiag, ∑ p ∈ P,
          (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
            Real.log p * realPairIndicator side omega e := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ (Finset.univ : Finset T).offDiag,
        (Real.log (Normalized.normalizedSum e.1 e.2) *
            realPairIndicator side omega e -
          (∑ p ∈ P,
            (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
              Real.log p * realPairIndicator side omega e)) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [ambientGapWeight]
      rw [← Finset.sum_mul]
      ring

/-- On the good-size event, the selected `A-B_P` potential retains the
universal good-event proportion of its full value. -/
theorem good_expect_selected_gap_ge
    (T P : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime) (hk : 0 < T.card)
    (side : T → Bool) :
    (3 / 16 - 12 / (T.card : ℝ)) *
        (AweightOrdered T - BPOrdered P T) ≤
      𝔼 omega : SystemSample T,
        if Good side T.card omega then
          AweightOrdered (selectedNat (selectedSet side omega)) -
            BPOrdered P (selectedNat (selectedSet side omega))
        else 0 := by
  let weight : T × T → ℝ := fun e =>
    if e.1 = e.2 then 0
    else ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ))
  have hgood := good_restricted_real_edgeMass_ge
    side T.card hk (by simp)
    weight
    (fun e => by
      by_cases hne : e.1 = e.2
      · simp [weight, hne]
      · simp only [weight, if_neg hne]
        exact ambientGapWeight_nonneg T P hT hprime e hne)
  have hweight_off : ∀ e ∈ (Finset.univ : Finset T).offDiag,
      weight e = ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ)) := by
    intro e he
    simp [weight, (Finset.mem_offDiag.mp he).2.2]
  have hedge (omega : SystemSample T) :
      (∑ e ∈ (Finset.univ : Finset T).offDiag,
          weight e * realPairIndicator side omega e) =
        ∑ e ∈ (Finset.univ : Finset T).offDiag,
          ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ)) *
            realPairIndicator side omega e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [hweight_off e he]
  have hweighttotal :
      (∑ e ∈ (Finset.univ : Finset T).offDiag, weight e) =
        ∑ e ∈ (Finset.univ : Finset T).offDiag,
          ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro e he
    exact hweight_off e he
  have hfull :
      (∑ e ∈ (Finset.univ : Finset T).offDiag,
        ambientGapWeight P ((e.1 : ℕ), (e.2 : ℕ))) =
        AweightOrdered T - BPOrdered P T := by
    have hs := SelectionBridge.sum_selectedNat_offDiag_eq
      (S := (Finset.univ : Finset T)) (ambientGapWeight P)
    have hsel : SelectionBridge.selectedNat (Finset.univ : Finset T) = T := by
      ext a
      simp [SelectionBridge.selectedNat]
    rw [hsel, sum_ambientGapWeight_eq] at hs
    exact hs.symm
  rw [hweighttotal, hfull] at hgood
  simp_rw [hedge] at hgood
  simp_rw [selected_gap_eq_indicator T P side]
  exact hgood

end

end Erdos126
