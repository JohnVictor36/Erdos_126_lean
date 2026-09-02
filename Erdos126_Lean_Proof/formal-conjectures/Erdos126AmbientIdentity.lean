import Erdos126Potentials

/-!
# The logged matching identity over an ambient prime set

After passing to a random subset, its additive prime support can be smaller
than the support of the original set.  The heavy prime must nevertheless stay
in the identity.  This file therefore states the factorization and matching
identity over any finite prime set containing the selected support.
-/

namespace Erdos126

open scoped BigOperators

noncomputable section

theorem AweightOrdered_eq_sum_normalisedSumVal_over
    (S P : Finset ℕ) (hS : ∀ a ∈ S, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : addPrimeSupport S ⊆ P) :
    AweightOrdered S =
      ∑ p ∈ P,
        ((∑ e ∈ S.offDiag, Padic.normalisedSumVal p e.1 e.2 : ℕ) : ℝ) *
          Real.log p := by
  rw [AweightOrdered]
  calc
    (∑ e ∈ S.offDiag, Real.log (Normalized.normalizedSum e.1 e.2)) =
        ∑ e ∈ S.offDiag, ∑ p ∈ P,
          (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ) *
            Real.log p := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_offDiag.mp he
      apply log_eq_sum_padicValNat_log_of_primeFactors_subset
        (Normalized.normalizedSum_pos (hS e.1 he'.1) (hS e.2 he'.2.1))
        P hprime
      exact (primeFactors_normalizedSum_subset_addPrimeSupport
        he'.1 he'.2.1 he'.2.2 (hS e.1 he'.1) (hS e.2 he'.2.1)).trans hsupport
    _ = ∑ p ∈ P, ∑ e ∈ S.offDiag,
          (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ) *
            Real.log p := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P,
        ((∑ e ∈ S.offDiag, Padic.normalisedSumVal p e.1 e.2 : ℕ) : ℝ) *
          Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_mul]
      congr 1
      norm_cast
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_offDiag.mp he
      exact padicValNat_normalizedSum_eq_normalisedSumVal
        (hS e.1 he'.1) (hS e.2 he'.2.1) (hprime p hp)

theorem BPOrdered_eq_sum_normalisedDiffVal_over
    (S P : Finset ℕ) (hS : ∀ a ∈ S, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime) :
    BPOrdered P S =
      ∑ p ∈ P,
        ((∑ e ∈ S.offDiag, Padic.normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) *
          Real.log p := by
  simp only [BPOrdered, BpOrdered]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_mul]
  congr 1
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_offDiag.mp he
  exact padicValNat_normalizedDist_eq_normalisedDiffVal
    (hS e.1 he'.1) (hS e.2 he'.2.1) (hprime p hp)

/-- Exact identity over an ambient prime set containing the sum support. -/
theorem logged_involution_identity_over
    (S P : Finset ℕ) (hS : ∀ a ∈ S, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : addPrimeSupport S ⊆ P)
    (τ : ℕ → S → S) :
    AweightOrdered S - BPOrdered P S +
        (∑ p ∈ P, Real.log p * pSlack p S (τ p)) =
      ∑ p ∈ P, Real.log p * (involutionCost p (τ p) : ℝ) := by
  rw [AweightOrdered_eq_sum_normalisedSumVal_over S P hS hprime hsupport,
    BPOrdered_eq_sum_normalisedDiffVal_over S P hS hprime]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [pSlack]
  ring

/-- Simultaneous p-adic optimization over the ambient prime set. -/
theorem exists_involutions_logged_identity_over
    (S P : Finset ℕ) (hS : ∀ a ∈ S, 0 < a)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : addPrimeSupport S ⊆ P) :
    ∃ τ : ℕ → S → S,
      (∀ p ∈ P, Function.Involutive (τ p)) ∧
      (∀ p ∈ P, 0 ≤ pSlack p S (τ p)) ∧
      AweightOrdered S - BPOrdered P S +
          (∑ p ∈ P, Real.log p * pSlack p S (τ p)) =
        ∑ p ∈ P, Real.log p * (involutionCost p (τ p) : ℝ) := by
  classical
  let τ : ℕ → S → S := fun p =>
    if hp : p.Prime then
      Classical.choose (Padic.exists_involution_weighted S p hp hS)
    else id
  refine ⟨τ, ?_, ?_, logged_involution_identity_over S P hS hprime hsupport τ⟩
  · intro p hpP
    have hp := hprime p hpP
    dsimp only [τ]
    rw [dif_pos hp]
    exact (Classical.choose_spec
      (Padic.exists_involution_weighted S p hp hS)).1
  · intro p hpP
    have hp := hprime p hpP
    have hspec := Classical.choose_spec
      (Padic.exists_involution_weighted S p hp hS)
    dsimp only [τ]
    rw [dif_pos hp]
    simp only [pSlack]
    exact sub_nonneg.mpr (by exact_mod_cast hspec.2)

end

end Erdos126
