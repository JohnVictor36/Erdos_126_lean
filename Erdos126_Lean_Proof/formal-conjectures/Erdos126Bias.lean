import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite averaging for the biased-selection step in Erdős problem 126

This file isolates the algebraic and finite-probability content of the biased
class selection.  It deliberately uses `Finset.expect`, rather than measure
theory.  The arithmetic lemma proves the exact `1 / 8` local slack.  The last
two lemmas give the finite Chebyshev truncation used to retain a subset of
linear size.
-/

open scoped BigOperators

namespace Erdos126.Bias

/-- The polynomial extension of `n.choose 2` from naturals to rationals. -/
def chooseTwoQ (x : ℚ) : ℚ := x * (x - 1) / 2

@[simp]
lemma chooseTwoQ_natCast (n : ℕ) : chooseTwoQ n = (n.choose 2 : ℚ) := by
  rw [chooseTwoQ, Nat.cast_choose_two]

lemma chooseTwoQ_nonneg_nat (n : ℕ) : 0 ≤ chooseTwoQ n := by
  rw [chooseTwoQ_natCast]
  positivity

/-- The exact algebra behind the one-component `1 / 8` slack estimate.

The three terms on the right are respectively the expected internal-pair
mass, minus the expected cross-pair mass, plus the contribution of an
arbitrary fixed matching of size `min c d`.
-/
theorem one_eighth_le_component_moment (c d : ℕ) :
    (1 / 8 : ℚ) * (chooseTwoQ c + chooseTwoQ d) ≤
      5 / 16 * (chooseTwoQ c + chooseTwoQ d) -
        3 / 16 * (c : ℚ) * d + 3 / 16 * ((min c d : ℕ) : ℚ) := by
  rcases le_total c d with hcd | hdc
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hcd
    rw [min_eq_left (Nat.le_add_right c e)]
    have he := chooseTwoQ_nonneg_nat e
    simp only [chooseTwoQ, Nat.cast_add] at he ⊢
    nlinarith
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdc
    rw [min_eq_right (Nat.le_add_right d e)]
    have he := chooseTwoQ_nonneg_nat e
    simp only [chooseTwoQ, Nat.cast_add] at he ⊢
    nlinarith

section Expectation

variable {Omega : Type*} [Fintype Omega]

/-- Monotonicity of uniform finite expectation. -/
lemma expect_mono {F G : Omega → ℚ} (h : ∀ omega, F omega ≤ G omega) :
    (𝔼 omega, F omega) ≤ 𝔼 omega, G omega := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  gcongr
  exact h i

/-- Moment form of the biased-class lemma.

The hypotheses are precisely the four elementary computations in the paper:
internal pairs survive with average `5 / 16`, cross pairs with `3 / 16`, and
a fixed matching contributes `3 min(c,d) / 16`.  The pointwise condition on
`R` says that the retained fixed-matching edges are no more numerous than a
maximum matching of the selected classes.
-/
theorem expected_component_slack
    (c d : ℕ) (X Y R : Omega → ℕ)
    (hpair :
      (𝔼 omega, (chooseTwoQ (X omega) + chooseTwoQ (Y omega))) =
        5 / 16 * (chooseTwoQ c + chooseTwoQ d))
    (hcross :
      (𝔼 omega, ((X omega : ℚ) * Y omega)) = 3 / 16 * (c : ℚ) * d)
    (hfixed :
      (𝔼 omega, ((R omega : ℚ))) = 3 / 16 * ((min c d : ℕ) : ℚ))
    (hR : ∀ omega, R omega ≤ min (X omega) (Y omega)) :
    (1 / 8 : ℚ) * (chooseTwoQ c + chooseTwoQ d) ≤
      𝔼 omega,
        (chooseTwoQ (X omega) + chooseTwoQ (Y omega) -
          (X omega : ℚ) * Y omega + ((min (X omega) (Y omega) : ℕ) : ℚ)) := by
  calc
    (1 / 8 : ℚ) * (chooseTwoQ c + chooseTwoQ d) ≤
        5 / 16 * (chooseTwoQ c + chooseTwoQ d) -
          3 / 16 * (c : ℚ) * d + 3 / 16 * ((min c d : ℕ) : ℚ) :=
      one_eighth_le_component_moment c d
    _ = 𝔼 omega,
          (chooseTwoQ (X omega) + chooseTwoQ (Y omega) -
            (X omega : ℚ) * Y omega + R omega) := by
      symm
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        hpair, hcross, hfixed]
    _ ≤ 𝔼 omega,
          (chooseTwoQ (X omega) + chooseTwoQ (Y omega) -
            (X omega : ℚ) * Y omega +
              ((min (X omega) (Y omega) : ℕ) : ℚ)) := by
      refine expect_mono (F := fun omega ↦
        chooseTwoQ (X omega) + chooseTwoQ (Y omega) -
          (X omega : ℚ) * Y omega + R omega) (G := fun omega ↦
        chooseTwoQ (X omega) + chooseTwoQ (Y omega) -
          (X omega : ℚ) * Y omega + ((min (X omega) (Y omega) : ℕ) : ℚ)) ?_
      intro omega
      gcongr
      exact Nat.cast_le.mpr (hR omega)

/-- Finite Chebyshev inequality for a uniform sample space.

It is stated in terms of the density of the exceptional finset, so no measure
theory is involved.
-/
theorem bad_density_le_secondMoment_div_sq [Nonempty Omega]
    (X : Omega → ℚ) (mu variance threshold : ℚ) (hthreshold : 0 < threshold)
    (hsecond : (𝔼 omega, (X omega - mu) ^ 2) ≤ variance) :
    (((Finset.univ.filter fun omega : Omega ↦
        threshold ≤ |X omega - mu|).card : ℕ) : ℚ) /
        Fintype.card Omega ≤ variance / threshold ^ 2 := by
  let bad : Finset Omega := {omega | threshold ≤ |X omega - mu|}
  have hpoint (omega : Omega) (homega : omega ∈ bad) :
      threshold ^ 2 ≤ (X omega - mu) ^ 2 := by
    have h := (Finset.mem_filter.mp homega).2
    nlinarith [sq_abs (X omega - mu)]
  have hsum :
      (bad.card : ℚ) * threshold ^ 2 ≤
        ∑ omega : Omega, (X omega - mu) ^ 2 := by
    calc
      (bad.card : ℚ) * threshold ^ 2 =
          ∑ omega ∈ bad, threshold ^ 2 := by simp
      _ ≤ ∑ omega ∈ bad, (X omega - mu) ^ 2 :=
        Finset.sum_le_sum fun omega homega ↦ hpoint omega homega
      _ ≤ ∑ omega : Omega, (X omega - mu) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
          (fun _ _ _ ↦ sq_nonneg _)
  have hcard : (0 : ℚ) < Fintype.card Omega := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  rw [Fintype.expect_eq_sum_div_card] at hsecond
  have hsum' :
      ∑ omega : Omega, (X omega - mu) ^ 2 ≤
        Fintype.card Omega * variance := by
    simpa [mul_comm] using (div_le_iff₀ hcard).mp hsecond
  have hmain := hsum.trans hsum'
  have hthresholdSq : 0 < threshold ^ 2 := sq_pos_of_pos hthreshold
  apply (div_le_iff₀ hcard).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hthresholdSq).mpr
  simpa [mul_comm] using hmain

/-- A variance bound for a count with mean at least `k / 4` gives a linear-size
subset outside a set of density at most `12 / k`.

For independent Bernoulli `1 / 4` indicators the second-moment hypothesis is
an equality.  In the biased construction these indicators can be coupled
below the actual selected set, so this is the only tail estimate needed.
-/
theorem density_small_le_twelve_div [Nonempty Omega]
    (k : ℕ) (hk : 0 < k) (X : Omega → ℚ) (hX : ∀ omega, 0 ≤ X omega)
    (hsecond :
      (𝔼 omega, (X omega - (k : ℚ) / 4) ^ 2) ≤ 3 * (k : ℚ) / 16) :
    (((Finset.univ.filter fun omega : Omega ↦
        X omega < (k : ℚ) / 8).card : ℕ) : ℚ) /
        Fintype.card Omega ≤ 12 / (k : ℚ) := by
  let bad : Finset Omega := {omega | X omega < (k : ℚ) / 8}
  let dev : Finset Omega :=
    {omega | (k : ℚ) / 8 ≤ |X omega - (k : ℚ) / 4|}
  have hsubset : bad ⊆ dev := by
    intro omega homega
    have hsmall := (Finset.mem_filter.mp homega).2
    have hnonneg := hX omega
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [abs_of_nonpos]
      · linarith
      · linarith
  have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
  have hcheb := bad_density_le_secondMoment_div_sq X ((k : ℚ) / 4)
    (3 * (k : ℚ) / 16) ((k : ℚ) / 8) (by positivity) hsecond
  have hcard : (0 : ℚ) < Fintype.card Omega := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  calc
    (bad.card : ℚ) / Fintype.card Omega ≤
        (dev.card : ℚ) / Fintype.card Omega := by
      gcongr
    _ ≤ (3 * (k : ℚ) / 16) / ((k : ℚ) / 8) ^ 2 := hcheb
    _ = 12 / (k : ℚ) := by field_simp; ring

/-- Removing a bad set of density `delta` from a finite expectation loses at
most `delta * B` when the random quantity lies in `[0,B]`.
-/
theorem expect_restrict_good_ge [Nonempty Omega]
    (F : Omega → ℚ) (Good : Omega → Prop) [DecidablePred Good]
    (B c delta : ℚ) (hB : 0 ≤ B)
    (_hFnonneg : ∀ omega, 0 ≤ F omega) (hFle : ∀ omega, F omega ≤ B)
    (haverage : c * B ≤ 𝔼 omega, F omega)
    (hbad :
      (((Finset.univ.filter fun omega : Omega ↦ ¬ Good omega).card : ℕ) : ℚ) /
        Fintype.card Omega ≤ delta) :
    (c - delta) * B ≤ 𝔼 omega, if Good omega then F omega else 0 := by
  let bad : Finset Omega := {omega | ¬ Good omega}
  have hcard : (0 : ℚ) < Fintype.card Omega := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hbadExpect :
      (𝔼 omega, if ¬ Good omega then F omega else 0) ≤ delta * B := by
    rw [Fintype.expect_eq_sum_div_card]
    calc
      (∑ omega : Omega, if ¬ Good omega then F omega else 0) /
          Fintype.card Omega =
          (∑ omega ∈ bad, F omega) / Fintype.card Omega := by
        congr 1
        rw [Finset.sum_filter]
      _ ≤ (bad.card * B) / Fintype.card Omega := by
        gcongr
        simpa using Finset.sum_le_card_nsmul bad F B fun omega _ ↦ hFle omega
      _ = ((bad.card : ℚ) / Fintype.card Omega) * B := by ring
      _ ≤ delta * B := mul_le_mul_of_nonneg_right hbad hB
  have hsplit :
      (𝔼 omega, F omega) =
        (𝔼 omega, if Good omega then F omega else 0) +
          𝔼 omega, if ¬ Good omega then F omega else 0 := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro omega _
    by_cases h : Good omega <;> simp [h]
  rw [hsplit] at haverage
  nlinarith

end Expectation

end Erdos126.Bias
