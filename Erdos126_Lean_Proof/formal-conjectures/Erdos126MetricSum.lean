import Erdos126MetricBridge
import Erdos126Potentials

/-!
# Summing the normalized metric bound over the relevant primes

This file turns the concrete `6 / N` permutation estimate into the exact
cross-multiplied form used by the global argument.
-/

namespace Erdos126

open scoped BigOperators

noncomputable section

private theorem sum_over_finset_subtype_pair
    (T : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i : T, ∑ j : T, f i j) = ∑ i ∈ T, ∑ j ∈ T, f i j := by
  symm
  rw [Finset.sum_subtype T (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_subtype T (fun _ => Iff.rfl)]

private theorem sum_product_eq_offDiag_of_diag_zero
    (T : Finset ℕ) (f : ℕ → ℕ → ℝ) (hdiag : ∀ a ∈ T, f a a = 0) :
    (∑ i ∈ T, ∑ j ∈ T, f i j) = ∑ e ∈ T.offDiag, f e.1 e.2 := by
  rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag T)]
  rw [Finset.sum_diag]
  have hz : ∑ a ∈ T, f a a = 0 := Finset.sum_eq_zero hdiag
  rw [hz, zero_add]

/-- One prime's logged endpoint cost is bounded by the normalized logarithmic
weight of the corresponding permutation edge. -/
theorem log_mul_involutionCost_le_perm_weight
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (p : ℕ) (hp : p.Prime) (τ : T → T) (hτ : Function.Involutive τ) :
    Real.log p * (involutionCost p τ : ℝ) ≤
      ∑ a : T, normalizedLogWeight Subtype.val a
        ((Equiv.ofBijective τ hτ.bijective) a) := by
  classical
  rw [involutionCost, ← Finset.univ_eq_attach]
  push_cast
  rw [Finset.mul_sum]
  simpa only [Equiv.ofBijective_apply] using
    (Finset.sum_le_sum fun a _ha ↦ by
      by_cases hfix : τ a = a
      · simp [hfix, normalizedLogWeight]
      · have hab : (a : ℕ) ≠ (τ a : ℕ) := by
          intro hab
          apply hfix
          exact Subtype.ext hab.symm
        have hfix' : a ≠ τ a := Ne.symm hfix
        have hU : 0 < Normalized.normalizedSum (a : ℕ) (τ a : ℕ) :=
          Normalized.normalizedSum_pos (hT a a.property)
            (hT (τ a) (τ a).property)
        have hone := sum_padicValNat_log_le_log hU {p} (by
          intro q hq
          have hqp : q = p := Finset.mem_singleton.mp hq
          simpa [hqp] using hp)
        simp only [Finset.sum_singleton] at hone
        rw [padicValNat_normalizedSum_eq_normalisedSumVal
          (hT a a.property) (hT (τ a) (τ a).property) hp] at hone
        simpa [hfix, hfix', normalizedLogWeight, hab, mul_comm] using hone)

/-- Cross-multiplied `6 / |T|` estimate for one involution. -/
theorem card_mul_log_mul_involutionCost_le_six_AweightOrdered
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (p : ℕ) (hp : p.Prime) (τ : T → T) (hτ : Function.Involutive τ) :
    (T.card : ℝ) * (Real.log p * (involutionCost p τ : ℝ)) ≤
      6 * AweightOrdered T := by
  classical
  let σ : Equiv.Perm T := Equiv.ofBijective τ hτ.bijective
  have hmetric := normalizedSum_perm_cost_le_six_total
    (a := fun x : T => (x : ℕ))
    (fun x => hT x x.property) Subtype.val_injective (by simpa using hcard) σ
  have hcost := log_mul_involutionCost_le_perm_weight T hT p hp τ hτ
  have hcardR : (T.card : ℝ) = Fintype.card T := by simp
  have hrepeat :
      (Finset.univ.sum fun a : T ↦ Finset.univ.sum fun _b : T ↦
        normalizedLogWeight Subtype.val a (σ a)) =
      (T.card : ℝ) *
        (Finset.univ.sum fun a : T ↦ normalizedLogWeight Subtype.val a (σ a)) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← hcardR]
  have htotal :
      (Finset.univ.sum fun a : T ↦ Finset.univ.sum fun b : T ↦
        normalizedLogWeight Subtype.val a b) = AweightOrdered T := by
    let f : ℕ → ℕ → ℝ := fun a b =>
      if a = b then 0 else Real.log (Normalized.normalizedSum a b)
    calc
      (∑ a : T, ∑ b : T, normalizedLogWeight Subtype.val a b) =
          ∑ a : T, ∑ b : T, f a b := by
        apply Finset.sum_congr rfl
        intro a _ha
        apply Finset.sum_congr rfl
        intro b _hb
        simp only [normalizedLogWeight, f]
        congr 1
        exact propext Subtype.val_injective.eq_iff.symm
      _ = ∑ a ∈ T, ∑ b ∈ T, f a b := sum_over_finset_subtype_pair T f
      _ = ∑ e ∈ T.offDiag, f e.1 e.2 :=
        sum_product_eq_offDiag_of_diag_zero T f (by simp [f])
      _ = AweightOrdered T := by
        rw [AweightOrdered]
        apply Finset.sum_congr rfl
        intro e he
        have hne := (Finset.mem_offDiag.mp he).2.2
        simp [f, hne]
  rw [hrepeat, htotal] at hmetric
  have hmul := mul_le_mul_of_nonneg_left hcost (by positivity : 0 ≤ (T.card : ℝ))
  exact hmul.trans hmetric

/-- Summed cross-multiplied metric estimate.  No division is used, so the
statement remains convenient at the boundary cases of later applications. -/
theorem card_mul_sum_log_involutionCost_le_six_card_mul_AweightOrdered
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (τ : ℕ → T → T)
    (hτ : ∀ p ∈ P, Function.Involutive (τ p)) :
    (T.card : ℝ) *
        (∑ p ∈ P, Real.log p * (involutionCost p (τ p) : ℝ)) ≤
      6 * (P.card : ℝ) * AweightOrdered T := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ p ∈ P, (T.card : ℝ) *
        (Real.log p * (involutionCost p (τ p) : ℝ))) ≤
        ∑ p ∈ P, 6 * AweightOrdered T := by
      exact Finset.sum_le_sum fun p hp ↦
        card_mul_log_mul_involutionCost_le_six_AweightOrdered
          T hT hcard p (hprime p hp) (τ p) (hτ p hp)
    _ = 6 * (P.card : ℝ) * AweightOrdered T := by
      simp
      ring

end

end Erdos126
