import Erdos126Support
import Erdos126Asymptotic

/-!
# Bridges from finite bounds to the asymptotic statement in Erdős problem 126

This file turns a uniform finite lower bound for the prime support of pairwise
sums into the `Tendsto` conclusion appearing in the official formulation.
-/

open Filter

namespace Erdos126

/-- A uniform lower bound on the number of primes supporting the off-diagonal
pairwise sums transfers to the maximal function in the official formulation.

The analytic hypothesis is deliberately stated separately: the finite
combinatorial argument supplies `hg`, while its growth estimate supplies
`hgrowth`. -/
theorem tendsto_maximalAddFactorsCard_of_uniform_lowerBound
    (f g : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f)
    (hg : ∀ n (A : Finset ℕ), A.card = n →
      g n ≤ (addPrimeSupport A).card)
    (hgrowth : Tendsto (fun n : ℕ => (g n : ℝ) / Real.log n) atTop atTop) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  have hgf : ∀ n, g n ≤ f n := lowerBound_le_maximalAddFactorsCard f g hf hg
  refine tendsto_atTop_mono' atTop ?_ hgrowth
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos (Nat.one_lt_cast.mpr hn)).le
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hgf n)) hlog

/-- An eventually uniform natural ceiling of a square-root lower bound is
enough to settle the asymptotic conclusion in the official formulation.  The
ceiling is the clean way to pass from a real-valued combinatorial estimate to
the natural-valued maximal function without losing an additive constant. -/
theorem tendsto_maximalAddFactorsCard_of_eventually_uniform_ceil_sqrt_lowerBound
    (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c) (hf : IsMaximalAddFactorsCard f)
    (hsqrt : ∀ᶠ n : ℕ in atTop, ∀ (A : Finset ℕ), A.card = n →
      ⌈c * Real.sqrt (n : ℝ)⌉₊ ≤ (addPrimeSupport A).card) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  have hceil : ∀ᶠ n : ℕ in atTop, ⌈c * Real.sqrt (n : ℝ)⌉₊ ≤ f n := by
    filter_upwards [hsqrt] with n hn
    exact le_maximalAddFactorsCard f hf hn
  have hff : ∀ᶠ n : ℕ in atTop, c * Real.sqrt (n : ℝ) ≤ (f n : ℝ) := by
    filter_upwards [hceil] with n hn
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  exact tendsto_div_log_atTop_of_eventually_sqrt_le f c hc hff

/-- A uniform square-root bound for cardinalities above two is a convenient
special case of the eventual transfer theorem. -/
theorem tendsto_maximalAddFactorsCard_of_uniform_ceil_sqrt_lowerBound_above_two
    (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c) (hf : IsMaximalAddFactorsCard f)
    (hsqrt : ∀ n (A : Finset ℕ), A.card = n →
      2 < n → ⌈c * Real.sqrt (n : ℝ)⌉₊ ≤ (addPrimeSupport A).card) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  apply tendsto_maximalAddFactorsCard_of_eventually_uniform_ceil_sqrt_lowerBound
    f c hc hf
  filter_upwards [eventually_gt_atTop 2] with n hn
  intro A hcard
  exact hsqrt n A hcard hn

/-- A finite estimate `n ≤ C * r²`, uniform over all `n`-element sets once
`n > 2` and with `r` the number of prime divisors of their off-diagonal sums,
already implies the asymptotic conclusion.  We use the slightly weaker but
cleaner bound `r ≥ sqrt n / C`; it is enough because `C` is fixed and positive. -/
theorem tendsto_maximalAddFactorsCard_of_card_le_const_mul_support_sq
    (f : ℕ → ℕ) (C : ℕ) (hC : 0 < C) (hf : IsMaximalAddFactorsCard f)
    (hquad : ∀ n (A : Finset ℕ), A.card = n →
      2 < n → n ≤ C * (addPrimeSupport A).card ^ 2) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  apply tendsto_maximalAddFactorsCard_of_eventually_uniform_ceil_sqrt_lowerBound
    f (1 / (C : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hC)) hf
  filter_upwards [eventually_gt_atTop 2] with n hn
  intro A hcard
  let r := (addPrimeSupport A).card
  have hquadN : n ≤ C * r ^ 2 := hquad n A hcard hn
  have hquadR : (n : ℝ) ≤ (C : ℝ) * (r : ℝ) ^ 2 := by
    exact_mod_cast hquadN
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hsqrt : Real.sqrt (n : ℝ) ≤ (C : ℝ) * r := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((C : ℝ) * r)]
  apply Nat.ceil_le.mpr
  rw [one_div, inv_mul_eq_div]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hC)).mpr (by simpa [mul_comm] using hsqrt)

end Erdos126
