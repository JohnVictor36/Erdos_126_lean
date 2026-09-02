import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
Auxiliary metric inequalities for the proposed proof of Erdős problem 126.

This file is deliberately separate from the official problem statement. The first
inequality is the abstract heart of the matching-cost estimate. The second is its
bipartite, three-step analogue.
-/

open scoped BigOperators

namespace Erdos126

section OnePart

variable {ι : Type*} [Fintype ι]

/-- Summed triangle inequality for a permutation of a finite type.

No symmetry or separation axiom is needed. If the permutation swaps the endpoints
of a matching and fixes every other vertex, its left side is twice the matching cost.
-/
theorem sum_perm_le_total_of_triangle
    (ρ : ι → ι → ℝ)
    (htriangle : ∀ i j k, ρ i k ≤ ρ i j + ρ j k)
    (σ : Equiv.Perm ι) :
    (∑ i : ι, ∑ _j : ι, ρ i (σ i)) ≤
      2 * ∑ i : ι, ∑ j : ι, ρ i j := by
  calc
    (∑ i : ι, ∑ _j : ι, ρ i (σ i))
        ≤ ∑ i : ι, ∑ j : ι, (ρ i j + ρ j (σ i)) := by
          exact Finset.sum_le_sum fun i _ ↦
            Finset.sum_le_sum fun j _ ↦ htriangle i j (σ i)
    _ = (∑ i : ι, ∑ j : ι, ρ i j) +
          (∑ i : ι, ∑ j : ι, ρ j (σ i)) := by
          simp only [Finset.sum_add_distrib]
    _ = (∑ i : ι, ∑ j : ι, ρ i j) +
          (∑ j : ι, ∑ i : ι, ρ j i) := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          exact Function.Bijective.sum_comp σ.bijective (fun i ↦ ρ j i)
    _ = 2 * ∑ i : ι, ∑ j : ι, ρ i j := by ring

end OnePart

section Bipartite

variable {α β γ : Type*} [Fintype α] [Fintype β]

/-- A complete bipartite matching has small total cost in any ambient
triangle-distance. The right side is the sum of the three legs of the path
`a i`, `b l`, `a j`, `b (σ i)` over all triples.
-/
theorem sum_bipartite_equiv_le_total_of_triangle
    (ρ : γ → γ → ℝ)
    (hsymm : ∀ x y, ρ x y = ρ y x)
    (htriangle : ∀ x y z, ρ x z ≤ ρ x y + ρ y z)
    (a : α → γ) (b : β → γ) (σ : α ≃ β) :
    (Finset.univ.sum fun i : α ↦
      Finset.univ.sum fun _j : α ↦
        Finset.univ.sum fun _l : β ↦ ρ (a i) (b (σ i))) ≤
    Finset.univ.sum fun i : α ↦
      Finset.univ.sum fun j : α ↦
        Finset.univ.sum fun l : β ↦
          (ρ (a i) (b l) + ρ (a j) (b l)) + ρ (a j) (b (σ i)) := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro l _
  calc
    ρ (a i) (b (σ i)) ≤ ρ (a i) (b l) + ρ (b l) (b (σ i)) :=
      htriangle (a i) (b l) (b (σ i))
    _ ≤ ρ (a i) (b l) + (ρ (b l) (a j) + ρ (a j) (b (σ i))) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (htriangle (b l) (a j) (b (σ i))) (ρ (a i) (b l))
    _ = (ρ (a i) (b l) + ρ (a j) (b l)) + ρ (a j) (b (σ i)) := by
      rw [hsymm (b l) (a j)]
      ring

/-- Translation does not change a bipartite sum. -/
theorem add_translate_sub_translate
    (a b c : ℤ) : (a + c) + (b - c) = a + b := by
  ring

end Bipartite

end Erdos126
