import Erdos126Factorization
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# Removing zero from a finite set

The normalized arithmetic is most naturally stated for positive integers.
This file transfers a finite prime-support estimate from positive finsets to
arbitrary finsets of naturals by erasing the possible element zero.
-/

namespace Erdos126

/-- Additive prime support is monotone under inclusion of the underlying
finsets. -/
theorem addPrimeSupport_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    addPrimeSupport A ⊆ addPrimeSupport B := by
  intro p hp
  rw [addPrimeSupport] at hp ⊢
  obtain ⟨ab, hab, hp⟩ := Finset.mem_biUnion.mp hp
  have hab' := Finset.mem_filter.mp hab
  have hoff := Finset.mem_offDiag.mp hab'.1
  apply Finset.mem_biUnion.mpr
  exact ⟨ab, Finset.mem_filter.mpr
    ⟨Finset.mem_offDiag.mpr
      ⟨hAB hoff.1, hAB hoff.2.1, hoff.2.2⟩, hab'.2⟩, hp⟩

/-- Erasing zero leaves only positive naturals. -/
theorem pos_of_mem_erase_zero {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A.erase 0) : 0 < a := by
  have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
  exact Nat.pos_of_ne_zero hne

theorem erase_zero_all_pos (A : Finset ℕ) :
    ∀ a ∈ A.erase 0, 0 < a := by
  intro a ha
  exact pos_of_mem_erase_zero ha

/-- Erasing zero loses at most one element. -/
theorem card_le_card_erase_zero_add_one (A : Finset ℕ) :
    A.card ≤ (A.erase 0).card + 1 := by
  by_cases h0 : 0 ∈ A
  · exact (Finset.card_erase_add_one h0).ge
  · rw [Finset.erase_eq_of_notMem h0]
    omega

/-- Above the exceptional two-element range, the additive prime support is
nonempty. -/
theorem addPrimeSupport_nonempty_of_two_lt_card
    (A : Finset ℕ) (hcard : 2 < A.card) :
    (addPrimeSupport A).Nonempty := by
  have hex : ∃ a ∈ A, 2 ≤ a := by
    by_contra h
    push Not at h
    have hsub : A ⊆ Finset.range 2 := by
      intro a ha
      exact Finset.mem_range.mpr (h a ha)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega
  obtain ⟨a, ha, ha2⟩ := hex
  have herase : 0 < (A.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hbErase⟩ := Finset.card_pos.mp herase
  have hba : b ≠ a := (Finset.mem_erase.mp hbErase).1
  have hb : b ∈ A := (Finset.mem_erase.mp hbErase).2
  have hsum : a + b ≠ 1 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hsum
  refine ⟨p, (primeFactors_sum_subset_addPrimeSupport ha hb hba.symm) ?_⟩
  exact hp.mem_primeFactors hpdvd (by omega)

theorem one_le_addPrimeSupport_card
    (A : Finset ℕ) (hcard : 2 < A.card) :
    1 ≤ (addPrimeSupport A).card := by
  exact Finset.card_pos.mpr (addPrimeSupport_nonempty_of_two_lt_card A hcard)

/-- General zero-removal transfer.  The loss of one vertex changes `C` to
`C + 1`; the last step uses that the original support is nonempty. -/
theorem card_le_succ_mul_support_sq_of_positive_bound
    (C : ℕ)
    (hpositive : ∀ (T : Finset ℕ),
      (∀ a ∈ T, 0 < a) → 2 ≤ T.card →
        T.card ≤ C * (addPrimeSupport T).card ^ 2)
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ (C + 1) * (addPrimeSupport A).card ^ 2 := by
  let T := A.erase 0
  have hTA : T ⊆ A := by
    intro a ha
    exact (Finset.mem_erase.mp ha).2
  have hTpos : ∀ a ∈ T, 0 < a := by
    intro a ha
    exact pos_of_mem_erase_zero ha
  have hTcard : 2 ≤ T.card := by
    have hloss := card_le_card_erase_zero_add_one A
    change A.card ≤ T.card + 1 at hloss
    omega
  have hTbound : T.card ≤ C * (addPrimeSupport T).card ^ 2 :=
    hpositive T hTpos hTcard
  have hcardLoss : A.card ≤ T.card + 1 := by
    exact card_le_card_erase_zero_add_one A
  have hr : (addPrimeSupport T).card ≤ (addPrimeSupport A).card :=
    Finset.card_le_card (addPrimeSupport_mono hTA)
  have hrsq : (addPrimeSupport T).card ^ 2 ≤
      (addPrimeSupport A).card ^ 2 := Nat.pow_le_pow_left hr 2
  have hmul : C * (addPrimeSupport T).card ^ 2 ≤
      C * (addPrimeSupport A).card ^ 2 := Nat.mul_le_mul_left C hrsq
  have hrpos := one_le_addPrimeSupport_card A hcard
  calc
    A.card ≤ T.card + 1 := hcardLoss
    _ ≤ C * (addPrimeSupport T).card ^ 2 + 1 := Nat.add_le_add_right hTbound 1
    _ ≤ C * (addPrimeSupport A).card ^ 2 + 1 := Nat.add_le_add_right hmul 1
    _ ≤ (C + 1) * (addPrimeSupport A).card ^ 2 := by
      nlinarith [sq_nonneg ((addPrimeSupport A).card - 1)]

/-- In particular a positive-set coefficient `1600` transfers verbatim up to
the unavoidable one-unit coefficient adjustment. -/
theorem card_le_1601_mul_support_sq_of_positive_1600
    (hpositive : ∀ (T : Finset ℕ),
      (∀ a ∈ T, 0 < a) → 2 ≤ T.card →
        T.card ≤ 1600 * (addPrimeSupport T).card ^ 2)
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 1601 * (addPrimeSupport A).card ^ 2 := by
  simpa using card_le_succ_mul_support_sq_of_positive_bound
    1600 hpositive A hcard

/-- The coefficient `768` supplied by the positive global argument leaves
ample room for zero removal while retaining the advertised coefficient
`1600` in the official natural-number statement. -/
theorem card_le_1600_mul_support_sq_of_positive_768
    (hpositive : ∀ (T : Finset ℕ),
      (∀ a ∈ T, 0 < a) → 2 ≤ T.card →
        T.card ≤ 768 * (addPrimeSupport T).card ^ 2)
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 1600 * (addPrimeSupport A).card ^ 2 := by
  have h769 := card_le_succ_mul_support_sq_of_positive_bound
    768 hpositive A hcard
  exact h769.trans <| Nat.mul_le_mul_right _ (by norm_num : 769 ≤ 1600)

end Erdos126
