import Erdos126HeavySelectionBridge
import Erdos126RealGoodEvent

/-!
# The heavy-prime slack on the good-size event
-/

namespace Erdos126

open scoped BigOperators
open BiasedSample BiasGlobal GoodEvent
open HeavyPrimeBias HeavySelectionBridge SelectionBridge RealGoodEvent

noncomputable section

theorem selectedNormalizedDiffMass_le_normalizedDiffMass
    (T : Finset ℕ) (p : ℕ) (omega : SystemSample T) :
    selectedNormalizedDiffMass T p omega ≤ normalizedDiffMass T p := by
  unfold selectedNormalizedDiffMass normalizedDiffMass
  apply Finset.sum_le_sum
  intro e he
  have hv : (0 : ℚ) ≤ (Padic.normalisedDiffVal p e.1 e.2 : ℚ) := by positivity
  simpa using mul_le_mul_of_nonneg_left
    (GoodEvent.pairIndicator_le_one
      (fun a : T => Padic.pUnitSide p a) omega e) hv

theorem selectedPadicSlack_le_normalizedDiffMass
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) (tau : T → T)
    (htau : Function.Involutive tau) (omega : SystemSample T) :
    (selectedPadicSlack T p tau omega : ℝ) ≤
      (normalizedDiffMass T p : ℝ) := by
  obtain ⟨sigma, hsigma, hdom, hnonneg, hupper⟩ :=
    exists_selected_optimal_dominates_selectedPadicSlack
      T p hp hT tau htau omega
  calc
    (selectedPadicSlack T p tau omega : ℝ) ≤
        pSlack p
          (selectedNat
            (selectedSet (fun a : T => Padic.pUnitSide p a) omega)) sigma := hdom
    _ ≤ selectedDiffMass p
          (selectedNat
            (selectedSet (fun a : T => Padic.pUnitSide p a) omega)) := hupper
    _ = (selectedNormalizedDiffMass T p omega : ℚ) := by
      rw [← HeavySelectionBridge.selectedDiffMass_selectedNat_selectedSet]
      norm_num
    _ ≤ (normalizedDiffMass T p : ℚ) := by
      exact_mod_cast selectedNormalizedDiffMass_le_normalizedDiffMass T p omega

theorem normalizedDiffMass_mul_log_eq_BpOrdered
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    (normalizedDiffMass T p : ℝ) * Real.log p = BpOrdered p T := by
  unfold normalizedDiffMass BpOrdered
  push_cast
  rw [Finset.sum_mul]
  have hsel : SelectionBridge.selectedNat (Finset.univ : Finset T) = T := by
    ext a
    simp [SelectionBridge.selectedNat]
  have hedge :=
    SelectionBridge.selectedNat_offDiag (S := (Finset.univ : Finset T))
  rw [hsel] at hedge
  rw [hedge, Finset.sum_image SelectionBridge.edgeVal_injective.injOn]
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_offDiag.mp he
  simp only [SelectionBridge.edgeVal]
  rw [padicValNat_normalizedDist_eq_normalisedDiffVal
    (hT e.1 e.1.property) (hT e.2 e.2.property) hp]

/-- A fixed heavy-prime matching retains its `1/8` gain after restriction to
the good-size event, losing only `12/k` of the full difference mass. -/
theorem exists_good_heavy_slack
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) (hk : 0 < T.card) :
    ∃ tau : T → T, Function.Involutive tau ∧
      (1 / 8 - 12 / (T.card : ℝ)) * BpOrdered p T ≤
        𝔼 omega : SystemSample T,
          if Good (fun a : T => Padic.pUnitSide p a) T.card omega then
            Real.log p * (selectedPadicSlack T p tau omega : ℝ)
          else 0 := by
  obtain ⟨tau, htau, hfullQ⟩ :=
    exists_one_eighth_diffMass_le_expect_selectedPadicSlack T p hp hT
  refine ⟨tau, htau, ?_⟩
  let F : SystemSample T → ℝ := fun omega =>
    (selectedPadicSlack T p tau omega : ℝ)
  let B : ℝ := (normalizedDiffMass T p : ℝ)
  have hB : 0 ≤ B := by
    dsimp only [B, normalizedDiffMass]
    positivity
  have hFle : ∀ omega, F omega ≤ B := by
    intro omega
    exact selectedPadicSlack_le_normalizedDiffMass T p hp hT tau htau omega
  have hbad := RealGoodEvent.bad_selected_real_density_le_twelve_div
    (fun a : T => Padic.pUnitSide p a) T.card hk (by simp)
  have hrestrict := RealGoodEvent.expect_sub_badLoss_le_expect_restrict_good
    F (Good (fun a : T => Padic.pUnitSide p a) T.card)
    B (12 / (T.card : ℝ)) hB hFle hbad
  have hfullR : (1 / 8 : ℝ) * B ≤ 𝔼 omega : SystemSample T, F omega := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hfullQ
    rw [RealGoodEvent.ratCast_expect] at hc
    dsimp only [F, B]
    norm_num at hc ⊢
    exact hc
  have hgoodR : (1 / 8 - 12 / (T.card : ℝ)) * B ≤
      𝔼 omega : SystemSample T,
        if Good (fun a : T => Padic.pUnitSide p a) T.card omega then F omega
        else 0 := by
    linarith
  have hlog : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp.ne_zero))
  rw [← normalizedDiffMass_mul_log_eq_BpOrdered T p hp hT]
  calc
    (1 / 8 - 12 / (T.card : ℝ)) *
        ((normalizedDiffMass T p : ℝ) * Real.log p) =
        Real.log p * ((1 / 8 - 12 / (T.card : ℝ)) * B) := by
      simp only [B]
      ring
    _ ≤ Real.log p *
        (𝔼 omega : SystemSample T,
          if Good (fun a : T => Padic.pUnitSide p a) T.card omega then F omega
          else 0) := mul_le_mul_of_nonneg_left hgoodR hlog
    _ = 𝔼 omega : SystemSample T,
          if Good (fun a : T => Padic.pUnitSide p a) T.card omega then
            Real.log p * (selectedPadicSlack T p tau omega : ℝ)
          else 0 := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro omega homega
      by_cases hg : Good (fun a : T => Padic.pUnitSide p a) T.card omega
      · simp [F, hg]
      · simp [F, hg]

end

end Erdos126
