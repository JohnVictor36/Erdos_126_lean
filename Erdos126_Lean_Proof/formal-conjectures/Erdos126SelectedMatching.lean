import Erdos126Potentials

/-!
# Restricting and re-optimizing p-adic involutions on a selected subset

This file gives the deterministic bridge needed after selecting a subset.
A full involution is restricted by fixing vertices whose partners were not
retained.  Re-optimizing the matching cost on the selected set can only
increase the resulting p-adic slack.
-/

namespace Erdos126

open scoped BigOperators
open _root_.Erdos126.Padic

noncomputable section

/-- Inclusion of the subtype of a smaller finset into that of a larger one. -/
def subsetInclusion {T S : Finset ℕ} (hST : S ⊆ T) : S → T :=
  fun a => ⟨a, hST a.property⟩

theorem subsetInclusion_injective {T S : Finset ℕ} (hST : S ⊆ T) :
    Function.Injective (subsetInclusion hST) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : T => (x : ℕ)) h

/-- Restrict an involution to a selected subset: retain an edge if both
endpoints survive, and otherwise fix the surviving endpoint. -/
def restrictedInvolution {T S : Finset ℕ} (hST : S ⊆ T)
    (τ : T → T) (a : S) : S :=
  let aT := subsetInclusion hST a
  if h : (τ aT : ℕ) ∈ S then ⟨τ aT, h⟩ else a

theorem restrictedInvolution_involutive
    {T S : Finset ℕ} (hST : S ⊆ T) (τ : T → T)
    (hτ : Function.Involutive τ) :
    Function.Involutive (restrictedInvolution hST τ) := by
  classical
  intro a
  by_cases hpartner : (τ (subsetInclusion hST a) : ℕ) ∈ S
  · let b : S := ⟨τ (subsetInclusion hST a), hpartner⟩
    have hbT : subsetInclusion hST b = τ (subsetInclusion hST a) := by
      apply Subtype.ext
      rfl
    have hback : (τ (subsetInclusion hST b) : ℕ) ∈ S := by
      rw [hbT, hτ]
      exact a.property
    have hfirst : restrictedInvolution hST τ a = b := by
      rw [restrictedInvolution, dif_pos hpartner]
    rw [hfirst]
    rw [restrictedInvolution]
    rw [dif_pos hback]
    apply Subtype.ext
    change (τ (subsetInclusion hST b) : ℕ) = (a : ℕ)
    rw [hbT, hτ]
    rfl
  · simp [restrictedInvolution, hpartner]

/-- Matching endpoint mass of the full involution retained by `S`.  The two
membership tests are the deterministic pair indicator. -/
def selectedMatchingMass (p : ℕ) {T : Finset ℕ} (τ : T → T)
    (S : Finset ℕ) : ℕ :=
  ∑ a ∈ T.attach,
    if τ a ≠ a ∧ (a : ℕ) ∈ S ∧ (τ a : ℕ) ∈ S then
      normalisedSumVal p a (τ a)
    else 0

def selectedSumMass (p : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ e ∈ S.offDiag, normalisedSumVal p e.1 e.2

def selectedDiffMass (p : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ e ∈ S.offDiag, normalisedDiffVal p e.1 e.2

/-- Slack of the restricted full-set matching, measured on the selected
set. -/
def restrictedSelectedSlack (p : ℕ) {T : Finset ℕ} (τ : T → T)
    (S : Finset ℕ) : ℝ :=
  selectedDiffMass p S + selectedMatchingMass p τ S - selectedSumMass p S

/-- The endpoint cost of the restricted involution is exactly the
pair-indicator-selected endpoint mass of the original involution. -/
theorem involutionCost_restrictedInvolution
    (p : ℕ) {T S : Finset ℕ} (hST : S ⊆ T)
    (τ : T → T) (_hτ : Function.Involutive τ) :
    involutionCost p (restrictedInvolution hST τ) =
      selectedMatchingMass p τ S := by
  classical
  let ST := T.attach.filter fun a : T => (a : ℕ) ∈ S
  have hsource :
      (∑ a ∈ S.attach,
        if restrictedInvolution hST τ a ≠ a then
          normalisedSumVal p a (restrictedInvolution hST τ a)
        else 0) =
      ∑ a ∈ ST,
        if τ a ≠ a ∧ (τ a : ℕ) ∈ S then
          normalisedSumVal p a (τ a)
        else 0 := by
    apply Finset.sum_bij (fun a _ => subsetInclusion hST a)
    · intro a ha
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_attach _ _, a.property⟩
    · intro a ha b hb hab
      exact subsetInclusion_injective hST hab
    · intro a ha
      have haData := Finset.mem_filter.mp ha
      let b : S := ⟨a, haData.2⟩
      refine ⟨b, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      rfl
    · intro a ha
      by_cases hpS : (τ (subsetInclusion hST a) : ℕ) ∈ S
      · have hrestrict : restrictedInvolution hST τ a =
            ⟨τ (subsetInclusion hST a), hpS⟩ := by
          rw [restrictedInvolution, dif_pos hpS]
        rw [hrestrict]
        by_cases hfix : τ (subsetInclusion hST a) = subsetInclusion hST a
        · have hfixS : (⟨τ (subsetInclusion hST a), hpS⟩ : S) = a := by
            apply Subtype.ext
            exact congrArg (fun x : T => (x : ℕ)) hfix
          rw [if_neg (not_ne_iff.mpr hfixS)]
          rw [if_neg (fun h => h.1 hfix)]
        · have hneS : (⟨τ (subsetInclusion hST a), hpS⟩ : S) ≠ a := by
            intro h
            apply hfix
            apply Subtype.ext
            exact congrArg (fun x : S => (x : ℕ)) h
          rw [if_pos hneS]
          rw [if_pos ⟨hfix, hpS⟩]
          rfl
      · have hrestrict : restrictedInvolution hST τ a = a := by
          rw [restrictedInvolution, dif_neg hpS]
        simp [hrestrict, hpS]
  rw [involutionCost, hsource, selectedMatchingMass]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases haS : (a : ℕ) ∈ S
  · simp [haS]
  · simp [haS]

/-- No involution endpoint cost exceeds the total ordered sum mass. -/
theorem involutionCost_le_selectedSumMass
    (p : ℕ) (S : Finset ℕ) (σ : S → S) :
    involutionCost p σ ≤ selectedSumMass p S := by
  classical
  let A := S.attach.filter fun a : S => σ a ≠ a
  let E := Finset.image (fun a : S => ((a : ℕ), (σ a : ℕ))) A
  have hcost : involutionCost p σ =
      ∑ a ∈ A, normalisedSumVal p a (σ a) := by
    unfold involutionCost
    rw [Finset.sum_filter]
  have hsum :
      (∑ a ∈ A, normalisedSumVal p a (σ a)) =
        ∑ e ∈ E, normalisedSumVal p e.1 e.2 := by
    apply Finset.sum_bij (fun (a : S) _ => ((a : ℕ), (σ a : ℕ)))
    · intro a ha
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    · intro a ha b hb hab
      exact Subtype.ext (congrArg Prod.fst hab)
    · intro e he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact ⟨a, ha, rfl⟩
    · intro a ha
      rfl
  have hsubset : E ⊆ S.offDiag := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have hne := (Finset.mem_filter.mp ha).2
    apply Finset.mem_offDiag.mpr
    exact ⟨a.property, (σ a).property,
      fun h => hne (Subtype.ext h.symm)⟩
  rw [hcost, hsum]
  exact Finset.sum_le_sum_of_subset hsubset

/-- There is an involution of maximum endpoint cost on every finite set. -/
theorem exists_maximal_involutionCost (p : ℕ) (S : Finset ℕ) :
    ∃ σ : S → S, Function.Involutive σ ∧
      ∀ ρ : S → S, Function.Involutive ρ →
        involutionCost p ρ ≤ involutionCost p σ := by
  classical
  let candidates := (Finset.univ : Finset (S → S)).filter Function.Involutive
  have hid : id ∈ candidates := by
    simp [candidates, Function.Involutive]
  obtain ⟨σ, hσ, hmax⟩ :=
    Finset.exists_max_image candidates (involutionCost p) ⟨id, hid⟩
  refine ⟨σ, (Finset.mem_filter.mp hσ).2, ?_⟩
  intro ρ hρ
  exact hmax ρ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ⟩)

/-- Re-optimize on `S`.  The optimal selected slack dominates the slack of
the restricted full matching, is nonnegative by the weighted p-adic theorem,
and is at most the selected difference mass. -/
theorem exists_selected_optimal_involution
    (T S : Finset ℕ) (hST : S ⊆ T) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) (τ : T → T) (hτ : Function.Involutive τ) :
    ∃ σ : S → S, Function.Involutive σ ∧
      restrictedSelectedSlack p τ S ≤ pSlack p S σ ∧
      0 ≤ pSlack p S σ ∧
      pSlack p S σ ≤ selectedDiffMass p S := by
  classical
  have hS : ∀ a ∈ S, 0 < a := by
    intro a ha
    exact hT a (hST ha)
  obtain ⟨σ, hσ, hmax⟩ := exists_maximal_involutionCost p S
  obtain ⟨ρ, hρ, hweighted⟩ :=
    Padic.exists_involution_weighted S p hp hS
  have hrestrictInv : Function.Involutive (restrictedInvolution hST τ) :=
    restrictedInvolution_involutive hST τ hτ
  have hdomCost : selectedMatchingMass p τ S ≤ involutionCost p σ := by
    rw [← involutionCost_restrictedInvolution p hST τ hτ]
    exact hmax _ hrestrictInv
  have hwitness : selectedSumMass p S ≤
      selectedDiffMass p S + involutionCost p ρ := by
    simpa only [selectedSumMass, selectedDiffMass, involutionCost] using hweighted
  have hnonnegNat : selectedSumMass p S ≤
      selectedDiffMass p S + involutionCost p σ :=
    hwitness.trans (Nat.add_le_add_left (hmax ρ hρ) _)
  have hupperNat : involutionCost p σ ≤ selectedSumMass p S :=
    involutionCost_le_selectedSumMass p S σ
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · unfold restrictedSelectedSlack pSlack
    unfold selectedDiffMass selectedSumMass
    have hdomCostR : (selectedMatchingMass p τ S : ℝ) ≤ involutionCost p σ := by
      exact_mod_cast hdomCost
    linarith
  · unfold pSlack
    have hnonnegR : (selectedSumMass p S : ℝ) ≤
        selectedDiffMass p S + involutionCost p σ := by
      exact_mod_cast hnonnegNat
    simpa only [selectedSumMass, selectedDiffMass] using
      (sub_nonneg.mpr hnonnegR)
  · unfold pSlack
    have hupperR : (involutionCost p σ : ℝ) ≤ selectedSumMass p S := by
      exact_mod_cast hupperNat
    unfold selectedSumMass at hupperR
    unfold selectedDiffMass
    linarith

end

end Erdos126
