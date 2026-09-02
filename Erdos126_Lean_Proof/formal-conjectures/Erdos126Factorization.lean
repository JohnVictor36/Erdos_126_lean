import Erdos126Normalized
import Erdos126Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime-support and logarithmic factorization bookkeeping

This file records the finite-support identities needed to pass between
normalized pairwise sums and sums of their `p`-adic valuations.
-/

namespace Erdos126

open scoped BigOperators

/-- Every member of the additive prime support is prime. -/
theorem prime_of_mem_addPrimeSupport {A : Finset ℕ} {p : ℕ}
    (hp : p ∈ addPrimeSupport A) : p.Prime := by
  rw [addPrimeSupport] at hp
  obtain ⟨ab, _hab, hp⟩ := Finset.mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hp

/-- The prime factors of one sum represented by an off-diagonal pair are in
the global additive prime support. -/
theorem primeFactors_sum_subset_addPrimeSupport
    {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    (a + b).primeFactors ⊆ addPrimeSupport A := by
  intro p hp
  rw [addPrimeSupport]
  apply Finset.mem_biUnion.mpr
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, hlt⟩, hp⟩
  · exact (hab heq).elim
  · refine ⟨(b, a), Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hb, ha, hab.symm⟩, hgt⟩, ?_⟩
    simpa [Nat.add_comm] using hp

/-- Dividing a positive pairwise sum by its normalizer introduces no new
prime factor. -/
theorem primeFactors_normalizedSum_subset_addPrimeSupport
    {A : Finset ℕ} {a b : ℕ} (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b) (ha : 0 < a) (hb : 0 < b) :
    (Normalized.normalizedSum a b).primeFactors ⊆ addPrimeSupport A := by
  have hdiv : Normalized.normalizedSum a b ∣ a + b := by
    refine ⟨Normalized.normalizer a b, ?_⟩
    exact (Normalized.normalizedSum_mul_normalizer ha hb).symm
  exact (Nat.primeFactors_mono hdiv (Nat.add_pos_left ha b).ne').trans
    (primeFactors_sum_subset_addPrimeSupport haA hbA hab)

/-- If a positive integer has all its prime factors in a finite set of
primes, its logarithm is the corresponding finite sum of `p`-adic orders. -/
theorem log_eq_sum_padicValNat_log_of_primeFactors_subset
    {U : ℕ} (_hU : 0 < U) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hsupport : U.primeFactors ⊆ P) :
    Real.log U = ∑ p ∈ P, (padicValNat p U : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ U.primeFactors,
      (U.factorization p : ℝ) * Real.log p) = _
  calc
    (∑ p ∈ U.primeFactors, (U.factorization p : ℝ) * Real.log p) =
        ∑ p ∈ U.primeFactors, (padicValNat p U : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.factorization_def U (Nat.prime_of_mem_primeFactors hp)]
    _ = ∑ p ∈ P, (padicValNat p U : ℝ) * Real.log p := by
      apply Finset.sum_subset hsupport
      intro p hpP hpU
      have hfac : U.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hpU
      rw [← Nat.factorization_def U (hprime p hpP), hfac]
      simp

/-- Logarithmic factorization of one normalized sum over the common additive
prime support. -/
theorem log_normalizedSum_eq_sum_addPrimeSupport
    {A : Finset ℕ} {a b : ℕ} (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b) (ha : 0 < a) (hb : 0 < b) :
    Real.log (Normalized.normalizedSum a b) =
      ∑ p ∈ addPrimeSupport A,
        (padicValNat p (Normalized.normalizedSum a b) : ℝ) * Real.log p := by
  apply log_eq_sum_padicValNat_log_of_primeFactors_subset
    (Normalized.normalizedSum_pos ha hb)
  · intro p hp
    exact prime_of_mem_addPrimeSupport hp
  · exact primeFactors_normalizedSum_subset_addPrimeSupport haA hbA hab ha hb

/-- Finite edge and prime sums can be interchanged. -/
theorem sum_edges_sum_primes_comm
    {ι : Type*} [DecidableEq ι] (E : Finset ι) (P : Finset ℕ)
    (w : ι → ℕ → ℝ) :
    (∑ e ∈ E, ∑ p ∈ P, w e p) =
      ∑ p ∈ P, ∑ e ∈ E, w e p := by
  rw [Finset.sum_comm]

/-- Summed logarithmic factorization for any finite collection of
off-diagonal edges from a positive set. -/
theorem sum_log_normalizedSum_eq_sum_prime_sum_edge
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ A.offDiag) :
    (∑ e ∈ E, Real.log (Normalized.normalizedSum e.1 e.2)) =
      ∑ p ∈ addPrimeSupport A,
        ∑ e ∈ E,
          (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ) * Real.log p := by
  calc
    (∑ e ∈ E, Real.log (Normalized.normalizedSum e.1 e.2)) =
        ∑ e ∈ E, ∑ p ∈ addPrimeSupport A,
          (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_offDiag.mp (hE he)
      exact log_normalizedSum_eq_sum_addPrimeSupport
        he'.1 he'.2.1 he'.2.2 (hA e.1 he'.1) (hA e.2 he'.2.1)
    _ = ∑ p ∈ addPrimeSupport A,
          ∑ e ∈ E,
            (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ) * Real.log p :=
      sum_edges_sum_primes_comm E (addPrimeSupport A) _

/-- The same identity with the common logarithm factored outside each inner
edge sum. -/
theorem sum_log_normalizedSum_eq_sum_prime_weighted_edge_sum
    (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (E : Finset (ℕ × ℕ)) (hE : E ⊆ A.offDiag) :
    (∑ e ∈ E, Real.log (Normalized.normalizedSum e.1 e.2)) =
      ∑ p ∈ addPrimeSupport A,
        (∑ e ∈ E,
          (padicValNat p (Normalized.normalizedSum e.1 e.2) : ℝ)) * Real.log p := by
  rw [sum_log_normalizedSum_eq_sum_prime_sum_edge A hA E hE]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul]

end Erdos126
