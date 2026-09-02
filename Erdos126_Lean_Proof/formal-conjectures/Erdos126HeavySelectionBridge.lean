import Erdos126HeavyPrimeBias
import Erdos126SelectedMatching
import Erdos126SelectionBridge

/-!
# Comparing the heavy-prime sample with the selected-set matching slack

The probabilistic heavy-prime argument is written on the attached subtype
`T`, whereas the logarithmic potential identity is written on the natural
number finset obtained by forgetting the membership proofs.  This file shows
that the two p-adic slacks agree exactly (after the harmless `ℚ`-to-`ℝ`
coercion), and then re-optimizes the matching on the selected natural-number
finset.
-/

namespace Erdos126.HeavySelectionBridge

open scoped BigOperators
open Erdos126.Padic Erdos126.BiasedSample
open Erdos126.HeavyPrimeBias Erdos126.SelectionBridge

noncomputable section

theorem selectedDiffMass_selectedNat_selectedSet
    (T : Finset ℕ) (p : ℕ) (omega : SystemSample T) :
    (selectedDiffMass p
        (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) : ℚ) =
      selectedNormalizedDiffMass T p omega := by
  unfold selectedDiffMass selectedNormalizedDiffMass
  rw [sum_selectedNat_normalisedDiffVal_eq]
  push_cast
  exact sum_selectedSet_offDiag_eq_indicator
    (fun a : T => pUnitSide p a) omega
    (fun e : T × T => (normalisedDiffVal p e.1 e.2 : ℚ))

theorem selectedSumMass_selectedNat_selectedSet
    (T : Finset ℕ) (p : ℕ) (omega : SystemSample T) :
    (selectedSumMass p
        (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) : ℚ) =
      selectedNormalizedSumMass T p omega := by
  unfold selectedSumMass selectedNormalizedSumMass
  rw [sum_selectedNat_normalisedSumVal_eq]
  push_cast
  exact sum_selectedSet_offDiag_eq_indicator
    (fun a : T => pUnitSide p a) omega
    (fun e : T × T => (normalisedSumVal p e.1 e.2 : ℚ))

theorem selectedMatchingMass_selectedNat_selectedSet
    (T : Finset ℕ) (p : ℕ) (tau : T → T) (omega : SystemSample T) :
    (selectedMatchingMass p tau
        (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) : ℚ) =
      selectedNormalizedMatchingMass T p tau omega := by
  classical
  unfold selectedMatchingMass selectedNormalizedMatchingMass
  push_cast
  have hattach : T.attach = (Finset.univ : Finset T) := by
    ext a
    simp
  rw [hattach]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairIndicator_eq_selected_ite]
  have haNat : (a : ℕ) ∈
      selectedNat (selectedSet (fun x : T => pUnitSide p x) omega) ↔
      a ∈ selectedSet (fun x : T => pUnitSide p x) omega := by
    rw [mem_selectedNat]
    constructor
    · rintro ⟨haT, hmem⟩
      simpa using hmem
    · intro hmem
      exact ⟨a.property, by simpa using hmem⟩
  have htauNat : (tau a : ℕ) ∈
      selectedNat (selectedSet (fun x : T => pUnitSide p x) omega) ↔
      tau a ∈ selectedSet (fun x : T => pUnitSide p x) omega := by
    rw [mem_selectedNat]
    constructor
    · rintro ⟨haT, hmem⟩
      simpa using hmem
    · intro hmem
      exact ⟨(tau a).property, by simpa using hmem⟩
  by_cases hfix : tau a = a
  · simp [hfix]
  · by_cases hboth :
        a ∈ selectedSet (fun x : T => pUnitSide p x) omega ∧
          tau a ∈ selectedSet (fun x : T => pUnitSide p x) omega
    · rw [if_pos hboth]
      simp [hfix, haNat, htauNat, hboth]
    · rw [if_neg hboth]
      have hnotNat : ¬((a : ℕ) ∈
          selectedNat (selectedSet (fun x : T => pUnitSide p x) omega) ∧
          (tau a : ℕ) ∈
            selectedNat (selectedSet (fun x : T => pUnitSide p x) omega)) := by
        simpa only [haNat, htauNat] using hboth
      have hcond : ¬(tau a ≠ a ∧
          (a : ℕ) ∈
            selectedNat (selectedSet (fun x : T => pUnitSide p x) omega) ∧
          (tau a : ℕ) ∈
            selectedNat (selectedSet (fun x : T => pUnitSide p x) omega)) := by
        intro h
        exact hnotNat ⟨h.2.1, h.2.2⟩
      rw [if_neg hcond]
      simp [hfix]

/-- The slack of the restricted full-set involution is precisely the real
coercion of the rational heavy-prime random slack. -/
theorem restrictedSelectedSlack_eq_selectedPadicSlack
    (T : Finset ℕ) (p : ℕ) (tau : T → T) (omega : SystemSample T) :
    restrictedSelectedSlack p tau
        (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) =
      (selectedPadicSlack T p tau omega : ℝ) := by
  unfold restrictedSelectedSlack selectedPadicSlack
  rw [← selectedDiffMass_selectedNat_selectedSet T p omega,
    ← selectedMatchingMass_selectedNat_selectedSet T p tau omega,
    ← selectedSumMass_selectedNat_selectedSet T p omega]
  norm_num

/-- On every outcome, an optimal matching on the selected natural-number
set dominates the heavy-prime slack used in the expectation argument. -/
theorem exists_selected_optimal_dominates_selectedPadicSlack
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) (tau : T → T)
    (htau : Function.Involutive tau) (omega : SystemSample T) :
    ∃ sigma : selectedNat
          (selectedSet (fun a : T => pUnitSide p a) omega) →
        selectedNat (selectedSet (fun a : T => pUnitSide p a) omega),
      Function.Involutive sigma ∧
      (selectedPadicSlack T p tau omega : ℝ) ≤
        pSlack p
          (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) sigma ∧
      0 ≤ pSlack p
          (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) sigma ∧
      pSlack p
          (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) sigma ≤
        selectedDiffMass p
          (selectedNat (selectedSet (fun a : T => pUnitSide p a) omega)) := by
  let S := selectedNat
    (selectedSet (fun a : T => pUnitSide p a) omega)
  have hST : S ⊆ T := selectedNat_subset _
  obtain ⟨sigma, hsigma, hdom, hnonneg, hupper⟩ :=
    exists_selected_optimal_involution T S hST p hp hT tau htau
  refine ⟨sigma, hsigma, ?_, hnonneg, hupper⟩
  rw [← restrictedSelectedSlack_eq_selectedPadicSlack T p tau omega]
  exact hdom

end

end Erdos126.HeavySelectionBridge
