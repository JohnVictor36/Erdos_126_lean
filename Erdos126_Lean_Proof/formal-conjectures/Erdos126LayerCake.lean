import Erdos126Padic

/-!
# Generic layer-cake wrappers for Erdos problem 126

The p-adic module now contains the specialized involution and canonical
matching conversions. This file retains the two reusable abstract lemmas for
turning threshold-cardinality comparisons into weighted-sum comparisons.
-/

namespace Erdos126.Padic

open scoped BigOperators

/-- A pointwise comparison of all threshold-cardinality functions up to a
common bound implies the corresponding comparison of total weights. -/
theorem weighted_sum_le_of_threshold_cards
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (u : α → ℕ) (v : β → ℕ) (N : ℕ)
    (hu : ∀ x ∈ A, u x ≤ N) (hv : ∀ y ∈ B, v y ≤ N)
    (hthreshold : ∀ t < N,
      (A.filter fun x => t + 1 ≤ u x).card ≤
        (B.filter fun y => t + 1 ≤ v y).card) :
    (∑ x ∈ A, u x) ≤ ∑ y ∈ B, v y := by
  rw [← sum_card_threshold_eq_sum A u N hu,
    ← sum_card_threshold_eq_sum B v N hv]
  exact Finset.sum_le_sum fun t ht => hthreshold t (Finset.mem_range.mp ht)

/-- Affine version of `weighted_sum_le_of_threshold_cards`, with a second
family on the right carrying a fixed natural coefficient. -/
theorem weighted_sum_le_add_mul_of_threshold_cards
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (u : α → ℕ) (d : β → ℕ) (m : γ → ℕ) (c N : ℕ)
    (hu : ∀ x ∈ A, u x ≤ N) (hd : ∀ y ∈ B, d y ≤ N)
    (hm : ∀ z ∈ C, m z ≤ N)
    (hthreshold : ∀ t < N,
      (A.filter fun x => t + 1 ≤ u x).card ≤
        (B.filter fun y => t + 1 ≤ d y).card +
          c * (C.filter fun z => t + 1 ≤ m z).card) :
    (∑ x ∈ A, u x) ≤
      (∑ y ∈ B, d y) + c * ∑ z ∈ C, m z := by
  have huSum := sum_card_threshold_eq_sum A u N hu
  have hdSum := sum_card_threshold_eq_sum B d N hd
  have hmSum := sum_card_threshold_eq_sum C m N hm
  have hsum := Finset.sum_le_sum (s := Finset.range N) fun t ht =>
    hthreshold t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rwa [huSum, hdSum, hmSum] at hsum

end Erdos126.Padic
