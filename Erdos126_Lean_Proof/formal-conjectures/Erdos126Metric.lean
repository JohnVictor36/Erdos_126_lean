import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
The abstract metric inequality underlying the matching-cost estimate for
Erdős problem 126.
-/

open scoped BigOperators

namespace Erdos126

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

end Erdos126
