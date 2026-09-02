import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Final numerical comparison for Erdős problem 126

This file contains only the last real/natural algebra in the proposed
square-root argument.  It is independent of the arithmetic and probability
constructions.
-/

namespace Erdos126.Numerical

/-- The exact real inequality supplied by the expectation sandwich.

The constants `16` and `96` give `16 * 96 = 1536`. -/
theorem card_real_le_1536_mul_sq
    (A E : ℝ) (k r : ℕ)
    (hA : 0 < A) (hk : 0 < k) (hr : 0 < r)
    (hlower : (1 / (16 * (r : ℝ))) * A ≤ E)
    (hupper : E ≤ (96 * (r : ℝ) / (k : ℝ)) * A) :
    (k : ℝ) ≤ 1536 * (r : ℝ) ^ 2 := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hsandwich :
      (1 / (16 * (r : ℝ))) * A ≤
        (96 * (r : ℝ) / (k : ℝ)) * A := hlower.trans hupper
  have hcoeff :
      (1 / (16 * (r : ℝ))) ≤ 96 * (r : ℝ) / (k : ℝ) := by
    apply (mul_le_mul_iff_right₀ hA).mp
    simpa [mul_comm] using hsandwich
  have hmulK :
      (1 / (16 * (r : ℝ))) * (k : ℝ) ≤ 96 * (r : ℝ) := by
    exact (le_div_iff₀ hkR).mp hcoeff
  have hdiv :
      (k : ℝ) / (16 * (r : ℝ)) ≤ 96 * (r : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hmulK
  have hdenom : (0 : ℝ) < 16 * (r : ℝ) := by positivity
  have hcross := (div_le_iff₀ hdenom).mp hdiv
  nlinarith

/-- Integral form with the exact coefficient from the expectation
sandwich.  Keeping `1536` (rather than immediately weakening to `1600`)
leaves enough room to erase a possible zero in the official natural-number
formulation. -/
theorem card_le_1536_mul_sq
    (A E : ℝ) (k r : ℕ)
    (hA : 0 < A) (hk : 0 < k) (hr : 0 < r)
    (hlower : (1 / (16 * (r : ℝ))) * A ≤ E)
    (hupper : E ≤ (96 * (r : ℝ) / (k : ℝ)) * A) :
    k ≤ 1536 * r ^ 2 := by
  have h := card_real_le_1536_mul_sq A E k r hA hk hr hlower hupper
  exact_mod_cast h

/-- A safe integral weakening of `card_real_le_1536_mul_sq`. -/
theorem card_le_1600_mul_sq
    (A E : ℝ) (k r : ℕ)
    (hA : 0 < A) (hk : 0 < k) (hr : 0 < r)
    (hlower : (1 / (16 * (r : ℝ))) * A ≤ E)
    (hupper : E ≤ (96 * (r : ℝ) / (k : ℝ)) * A) :
    k ≤ 1600 * r ^ 2 := by
  have h1536 := card_real_le_1536_mul_sq A E k r hA hk hr hlower hupper
  have h1600 : (k : ℝ) ≤ 1600 * (r : ℝ) ^ 2 := by
    have hrsq : (0 : ℝ) ≤ (r : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  exact_mod_cast h1600

/-- The bounded range needs no expectation estimates: one support prime is
enough to absorb every `k ≤ 192` into the same safe constant. -/
theorem small_card_le_1600_mul_sq
    (k r : ℕ) (hk : k ≤ 192) (hr : 1 ≤ r) :
    k ≤ 1600 * r ^ 2 := by
  have hrsq : 1 ≤ r ^ 2 := by
    exact one_le_pow₀ hr
  calc
    k ≤ 192 := hk
    _ ≤ 1600 := by norm_num
    _ = 1600 * 1 := by ring
    _ ≤ 1600 * r ^ 2 := Nat.mul_le_mul_left 1600 hrsq

/-- Combined abstract finite/large-case wrapper.

Only the large branch has to provide the expectation sandwich. -/
theorem card_le_1600_mul_sq_of_large_bounds
    (A E : ℝ) (k r : ℕ)
    (hA : 0 < A) (hk : 0 < k) (hr : 0 < r)
    (hlarge : 192 < k →
      (1 / (16 * (r : ℝ))) * A ≤ E ∧
        E ≤ (96 * (r : ℝ) / (k : ℝ)) * A) :
    k ≤ 1600 * r ^ 2 := by
  by_cases hsmall : k ≤ 192
  · exact small_card_le_1600_mul_sq k r hsmall hr
  · have hklarge : 192 < k := Nat.lt_of_not_ge hsmall
    obtain ⟨hlower, hupper⟩ := hlarge hklarge
    exact card_le_1600_mul_sq A E k r hA hk hr hlower hupper

end Erdos126.Numerical
