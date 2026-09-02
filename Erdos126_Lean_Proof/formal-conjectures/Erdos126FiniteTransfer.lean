import FormalConjectures.ErdosProblems.«126»

/-!
# Finite quadratic-to-square-root transfer for Erdos problem 126

This module converts a uniform estimate of the form `n ≤ 1600 * r ^ 2`, needed
only above the finite exceptional range, into a natural-valued lower bound for
the maximal function in the official statement.
-/

namespace Erdos126

/-- The natural-valued lower bound extracted from an estimate of the form
`n ≤ 1600 * r ^ 2`. -/
def sqrtLowerBound (n : ℕ) : ℕ := Nat.sqrt n / 40

/-- The elementary numerical implication underlying the transfer to the
extremal function. -/
theorem sqrtLowerBound_le_of_le {n r : ℕ} (h : n ≤ 1600 * r ^ 2) :
    sqrtLowerBound n ≤ r := by
  apply Nat.div_le_of_le_mul
  calc
    Nat.sqrt n ≤ Nat.sqrt (1600 * r ^ 2) := Nat.sqrt_le_sqrt h
    _ = Nat.sqrt ((40 * r) ^ 2) := by ring_nf
    _ = 40 * r := Nat.sqrt_eq' _

/-- A uniform quadratic estimate for the number of prime divisors of
off-diagonal pairwise sums gives a square-root lower bound for the official
maximal function.  The cases of sets with at most two elements are automatic. -/
theorem sqrtLowerBound_le_maximalAddFactorsCard
    (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f)
    (hfinite : ∀ (A : Finset ℕ), 2 < A.card →
      A.card ≤ 1600 *
        (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card ^ 2) :
    ∀ n, sqrtLowerBound n ≤ f n := by
  intro n
  cases n with
  | zero =>
    simp [sqrtLowerBound]
  | succ n =>
    cases n with
    | zero => simp [sqrtLowerBound]
    | succ n =>
      cases n with
      | zero => simp [sqrtLowerBound]
      | succ n =>
        apply (hf (n + 3)).2
        change ∀ (A : Finset ℕ), A.card = n + 3 →
          sqrtLowerBound (n + 3) ≤
            (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card
        intro A hA
        apply sqrtLowerBound_le_of_le
        have hcard : 2 < A.card := by
          rw [hA]
          exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ n))
        simpa [hA] using hfinite A hcard

end Erdos126
