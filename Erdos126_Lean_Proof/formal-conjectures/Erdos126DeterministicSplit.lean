import Erdos126SideLabel
import Erdos126Potentials

/-!
# Deterministic splitting at one prime

For a fixed prime `p`, the threshold-independent unit label from
`Erdos126SideLabel` partitions a positive finite set into two parts.
Every positive normalized `p`-adic sum valuation crosses this partition,
whereas every positive normalized `p`-adic difference valuation stays in
one part.  Thus the full difference mass splits exactly between the two
parts, while the sum mass (and hence every matching cost) vanishes on each
part separately.
-/

namespace Erdos126

open scoped BigOperators
open _root_.Erdos126.Padic

noncomputable section

/-- The vertices having the specified canonical `p`-unit side. -/
def pSide (T : Finset ℕ) (p : ℕ) (side : Bool) : Finset ℕ :=
  T.filter fun a => pUnitSide p a = side

@[simp] theorem mem_pSide {T : Finset ℕ} {p a : ℕ} {side : Bool} :
    a ∈ pSide T p side ↔ a ∈ T ∧ pUnitSide p a = side := by
  simp [pSide]

theorem pSide_subset (T : Finset ℕ) (p : ℕ) (side : Bool) :
    pSide T p side ⊆ T := by
  intro a ha
  exact (mem_pSide.mp ha).1

theorem pSide_false_disjoint_true (T : Finset ℕ) (p : ℕ) :
    Disjoint (pSide T p false) (pSide T p true) := by
  rw [Finset.disjoint_left]
  intro a ha0 ha1
  have h0 := (mem_pSide.mp ha0).2
  have h1 := (mem_pSide.mp ha1).2
  simp_all

theorem pSide_false_union_true (T : Finset ℕ) (p : ℕ) :
    pSide T p false ∪ pSide T p true = T := by
  ext a
  cases hside : pUnitSide p a <;> simp [pSide, hside]

/-- The evident inclusion of one side into the ambient subtype. -/
def pSideInclusion (T : Finset ℕ) (p : ℕ) (side : Bool) :
    pSide T p side → T :=
  fun a => ⟨a, pSide_subset T p side a.property⟩

theorem pSideInclusion_injective (T : Finset ℕ) (p : ℕ) (side : Bool) :
    Function.Injective (pSideInclusion T p side) := by
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun x : T => (x : ℕ)) hab

private theorem bool_eq_true_of_ne_false {b : Bool} (h : b ≠ false) :
    b = true := by
  cases b <;> simp_all

/-- Glue maps on the two canonical sides to a map of the ambient set. -/
def gluePSideMaps (T : Finset ℕ) (p : ℕ)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true) : T → T :=
  fun a =>
    if h0 : pUnitSide p a = false then
      pSideInclusion T p false
        (τ0 ⟨a, mem_pSide.mpr ⟨a.property, h0⟩⟩)
    else
      pSideInclusion T p true
        (τ1 ⟨a, mem_pSide.mpr
          ⟨a.property, bool_eq_true_of_ne_false h0⟩⟩)

@[simp] theorem gluePSideMaps_pSideInclusion_false
    (T : Finset ℕ) (p : ℕ)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true)
    (a : pSide T p false) :
    gluePSideMaps T p τ0 τ1 (pSideInclusion T p false a) =
      pSideInclusion T p false (τ0 a) := by
  have ha : pUnitSide p (a : ℕ) = false := (mem_pSide.mp a.property).2
  simp [gluePSideMaps, pSideInclusion, ha]

@[simp] theorem gluePSideMaps_pSideInclusion_true
    (T : Finset ℕ) (p : ℕ)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true)
    (a : pSide T p true) :
    gluePSideMaps T p τ0 τ1 (pSideInclusion T p true a) =
      pSideInclusion T p true (τ1 a) := by
  have ha : pUnitSide p (a : ℕ) = true := (mem_pSide.mp a.property).2
  simp [gluePSideMaps, pSideInclusion, ha]

/-- Gluing involutions on the two sides gives an ambient involution. -/
theorem gluePSideMaps_involutive
    (T : Finset ℕ) (p : ℕ)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true)
    (hτ0 : Function.Involutive τ0) (hτ1 : Function.Involutive τ1) :
    Function.Involutive (gluePSideMaps T p τ0 τ1) := by
  intro a
  by_cases h0 : pUnitSide p a = false
  · let a0 : pSide T p false :=
      ⟨a, mem_pSide.mpr ⟨a.property, h0⟩⟩
    have ha : a = pSideInclusion T p false a0 := by
      apply Subtype.ext
      rfl
    rw [ha, gluePSideMaps_pSideInclusion_false,
      gluePSideMaps_pSideInclusion_false, hτ0]
  · have h1 : pUnitSide p a = true := bool_eq_true_of_ne_false h0
    let a1 : pSide T p true :=
      ⟨a, mem_pSide.mpr ⟨a.property, h1⟩⟩
    have ha : a = pSideInclusion T p true a1 := by
      apply Subtype.ext
      rfl
    rw [ha, gluePSideMaps_pSideInclusion_true,
      gluePSideMaps_pSideInclusion_true, hτ1]

/-- Endpoint costs add under gluing, for an arbitrary valuation prime `q`.
The prime used to cut the two sides need not equal `q`. -/
theorem involutionCost_gluePSideMaps
    (T : Finset ℕ) (p q : ℕ)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true) :
    involutionCost q (gluePSideMaps T p τ0 τ1) =
      involutionCost q τ0 + involutionCost q τ1 := by
  classical
  unfold involutionCost
  rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach,
    ← Finset.univ_eq_attach]
  let F0 : Finset T :=
    Finset.univ.filter fun a : T => pUnitSide p a = false
  let F1 : Finset T :=
    Finset.univ.filter fun a : T => pUnitSide p a = true
  have hdisj : Disjoint F0 F1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    have h0 := (Finset.mem_filter.mp ha0).2
    have h1 := (Finset.mem_filter.mp ha1).2
    simp_all
  have hpart : F0 ∪ F1 = (Finset.univ : Finset T) := by
    ext a
    cases hside : pUnitSide p a <;> simp [F0, F1, hside]
  rw [← hpart, Finset.sum_union hdisj]
  congr 1
  · symm
    apply Finset.sum_bij
      (fun a _ => pSideInclusion T p false a)
    · intro a ha
      have hside := (mem_pSide.mp a.property).2
      simp [F0, pSideInclusion, hside]
    · intro a ha b hb hab
      exact pSideInclusion_injective T p false hab
    · intro a ha
      have hside : pUnitSide p a = false := by
        exact (Finset.mem_filter.mp ha).2
      let a0 : pSide T p false :=
        ⟨a, mem_pSide.mpr ⟨a.property, hside⟩⟩
      refine ⟨a0, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      rfl
    · intro a ha
      change
        (if τ0 a ≠ a then normalisedSumVal q (a : ℕ) (τ0 a : ℕ) else 0) =
          (if gluePSideMaps T p τ0 τ1
                (pSideInclusion T p false a) ≠
                pSideInclusion T p false a then
            normalisedSumVal q (a : ℕ)
              (gluePSideMaps T p τ0 τ1
                (pSideInclusion T p false a) : ℕ)
          else 0)
      rw [gluePSideMaps_pSideInclusion_false]
      by_cases hfix : τ0 a = a
      · simp [hfix]
      · simp [hfix, pSideInclusion]
  · symm
    apply Finset.sum_bij
      (fun a _ => pSideInclusion T p true a)
    · intro a ha
      have hside := (mem_pSide.mp a.property).2
      simp [F1, pSideInclusion, hside]
    · intro a ha b hb hab
      exact pSideInclusion_injective T p true hab
    · intro a ha
      have hside : pUnitSide p a = true := by
        exact (Finset.mem_filter.mp ha).2
      let a1 : pSide T p true :=
        ⟨a, mem_pSide.mpr ⟨a.property, hside⟩⟩
      refine ⟨a1, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      rfl
    · intro a ha
      change
        (if τ1 a ≠ a then normalisedSumVal q (a : ℕ) (τ1 a : ℕ) else 0) =
          (if gluePSideMaps T p τ0 τ1
                (pSideInclusion T p true a) ≠
                pSideInclusion T p true a then
            normalisedSumVal q (a : ℕ)
              (gluePSideMaps T p τ0 τ1
                (pSideInclusion T p true a) : ℕ)
          else 0)
      rw [gluePSideMaps_pSideInclusion_true]
      by_cases hfix : τ1 a = a
      · simp [hfix]
      · simp [hfix, pSideInclusion]

/-- A normalized sum valuation vanishes when its endpoints have the same
canonical side. -/
theorem normalisedSumVal_eq_zero_of_same_pUnitSide
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hsame : pUnitSide p a = pUnitSide p b) :
    normalisedSumVal p a b = 0 := by
  by_contra hne
  have hpos : 0 < normalisedSumVal p a b := Nat.pos_of_ne_zero hne
  have hopposite := pUnitSide_ne_of_normalisedSumVal_threshold
    hp ha hb (n := 1) (by omega) hpos
  exact hopposite hsame

/-- A normalized difference valuation vanishes when its endpoints have
different canonical sides. -/
theorem normalisedDiffVal_eq_zero_of_ne_pUnitSide
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hside : pUnitSide p a ≠ pUnitSide p b) :
    normalisedDiffVal p a b = 0 := by
  have hab : a ≠ b := by
    intro hab
    apply hside
    rw [hab]
  by_contra hne
  have hpos : 0 < normalisedDiffVal p a b := Nat.pos_of_ne_zero hne
  have hequal := pUnitSide_eq_of_normalisedDiffVal_threshold
    hp ha hb hab (n := 1) (by omega) hpos
  exact hside hequal

theorem normalisedSumVal_eq_zero_of_mem_pSide
    {T : Finset ℕ} {p a b : ℕ} {side : Bool}
    (hp : p.Prime) (hT : ∀ x ∈ T, 0 < x)
    (ha : a ∈ pSide T p side) (hb : b ∈ pSide T p side) :
    normalisedSumVal p a b = 0 := by
  apply normalisedSumVal_eq_zero_of_same_pUnitSide hp
    (hT a (mem_pSide.mp ha).1) (hT b (mem_pSide.mp hb).1)
  exact (mem_pSide.mp ha).2.trans (mem_pSide.mp hb).2.symm

theorem normalisedDiffVal_eq_zero_of_mem_opposite_pSides
    {T : Finset ℕ} {p a b : ℕ} {side : Bool}
    (hp : p.Prime) (hT : ∀ x ∈ T, 0 < x)
    (ha : a ∈ pSide T p side) (hb : b ∈ pSide T p (!side)) :
    normalisedDiffVal p a b = 0 := by
  apply normalisedDiffVal_eq_zero_of_ne_pUnitSide hp
    (hT a (mem_pSide.mp ha).1) (hT b (mem_pSide.mp hb).1)
  have haSide := (mem_pSide.mp ha).2
  have hbSide := (mem_pSide.mp hb).2
  cases side <;> simp_all

/-- Every ordered normalized sum valuation internal to one side is zero. -/
theorem sum_normalisedSumVal_pSide_eq_zero
    (T : Finset ℕ) (p : ℕ) (side : Bool)
    (hp : p.Prime) (hT : ∀ a ∈ T, 0 < a) :
    ∑ e ∈ (pSide T p side).offDiag,
        normalisedSumVal p e.1 e.2 = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hedge := Finset.mem_offDiag.mp he
  exact normalisedSumVal_eq_zero_of_mem_pSide hp hT hedge.1 hedge.2.1

/-- Therefore every involution on one side has zero normalized `p`-sum
endpoint cost. -/
theorem involutionCost_pSide_eq_zero
    (T : Finset ℕ) (p : ℕ) (side : Bool)
    (hp : p.Prime) (hT : ∀ a ∈ T, 0 < a)
    (τ : pSide T p side → pSide T p side) :
    involutionCost p τ = 0 := by
  unfold involutionCost
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hfix : τ a = a
  · simp [hfix]
  · rw [if_pos hfix]
    exact normalisedSumVal_eq_zero_of_mem_pSide hp hT a.property (τ a).property

/-- On one side, the unlogged matching slack is exactly its normalized
difference mass. -/
theorem pSlack_pSide_eq_diffMass
    (T : Finset ℕ) (p : ℕ) (side : Bool)
    (hp : p.Prime) (hT : ∀ a ∈ T, 0 < a)
    (τ : pSide T p side → pSide T p side) :
    pSlack p (pSide T p side) τ =
      ((∑ e ∈ (pSide T p side).offDiag,
        normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) := by
  unfold pSlack
  rw [involutionCost_pSide_eq_zero T p side hp hT τ,
    sum_normalisedSumVal_pSide_eq_zero T p side hp hT]
  norm_num

private theorem sum_offDiag_eq_sum_product_of_diag_zero
    {V : Type*} [DecidableEq V]
    (S : Finset V) (f : V → V → ℕ)
    (hdiag : ∀ a ∈ S, f a a = 0) :
    (∑ e ∈ S.offDiag, f e.1 e.2) =
      ∑ a ∈ S, ∑ b ∈ S, f a b := by
  rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag S)]
  rw [Finset.sum_diag]
  have hz : ∑ a ∈ S, f a a = 0 := Finset.sum_eq_zero hdiag
  rw [hz, zero_add]

private theorem sum_offDiag_eq_add_of_partition_of_cross_zero
    {V : Type*} [DecidableEq V]
    (T S U : Finset V) (f : V → V → ℕ)
    (hpart : S ∪ U = T) (hdisj : Disjoint S U)
    (hdiag : ∀ a ∈ T, f a a = 0)
    (hSU : ∀ a ∈ S, ∀ b ∈ U, f a b = 0)
    (hUS : ∀ a ∈ U, ∀ b ∈ S, f a b = 0) :
    (∑ e ∈ T.offDiag, f e.1 e.2) =
      (∑ e ∈ S.offDiag, f e.1 e.2) +
        ∑ e ∈ U.offDiag, f e.1 e.2 := by
  have hST : S ⊆ T := by
    rw [← hpart]
    exact Finset.subset_union_left
  have hUT : U ⊆ T := by
    rw [← hpart]
    exact Finset.subset_union_right
  rw [sum_offDiag_eq_sum_product_of_diag_zero T f hdiag,
    sum_offDiag_eq_sum_product_of_diag_zero S f
      (fun a ha => hdiag a (hST ha)),
    sum_offDiag_eq_sum_product_of_diag_zero U f
      (fun a ha => hdiag a (hUT ha)), ← hpart]
  rw [Finset.sum_union hdisj]
  simp_rw [Finset.sum_union hdisj]
  have hzSU : ∑ a ∈ S, ∑ b ∈ U, f a b = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    exact hSU a ha b hb
  have hzUS : ∑ a ∈ U, ∑ b ∈ S, f a b = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    exact hUS a ha b hb
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hzSU, hzUS]
  omega

/-- The full ordered normalized difference mass is exactly the sum of the
two internal side masses. -/
theorem sum_normalisedDiffVal_pSide_partition
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    (∑ e ∈ T.offDiag, normalisedDiffVal p e.1 e.2) =
      (∑ e ∈ (pSide T p false).offDiag,
        normalisedDiffVal p e.1 e.2) +
      ∑ e ∈ (pSide T p true).offDiag,
        normalisedDiffVal p e.1 e.2 := by
  apply sum_offDiag_eq_add_of_partition_of_cross_zero
    T (pSide T p false) (pSide T p true)
    (fun a b => normalisedDiffVal p a b)
    (pSide_false_union_true T p) (pSide_false_disjoint_true T p)
  · intro a ha
    simp [normalisedDiffVal]
  · intro a ha b hb
    exact normalisedDiffVal_eq_zero_of_mem_opposite_pSides
      hp hT ha (by simpa using hb)
  · intro a ha b hb
    rw [normalisedDiffVal_comm]
    exact normalisedDiffVal_eq_zero_of_mem_opposite_pSides hp hT hb
      (by simpa using ha)

/-- Convert one ordered normalized difference mass to its logged `BpOrdered`
form. -/
theorem diffMass_mul_log_eq_BpOrdered
    (S : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hS : ∀ a ∈ S, 0 < a) :
    ((∑ e ∈ S.offDiag, normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) *
        Real.log p = BpOrdered p S := by
  unfold BpOrdered
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have hedge := Finset.mem_offDiag.mp he
  rw [padicValNat_normalizedDist_eq_normalisedDiffVal
    (hS e.1 hedge.1) (hS e.2 hedge.2.1) hp]

/-- Logged form of the exact partition identity. -/
theorem BpOrdered_pSide_partition
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    BpOrdered p T =
      BpOrdered p (pSide T p false) +
        BpOrdered p (pSide T p true) := by
  have hmass := sum_normalisedDiffVal_pSide_partition T p hp hT
  rw [← diffMass_mul_log_eq_BpOrdered T p hp hT,
    ← diffMass_mul_log_eq_BpOrdered (pSide T p false) p hp
      (fun a ha => hT a (pSide_subset T p false ha)),
    ← diffMass_mul_log_eq_BpOrdered (pSide T p true) p hp
      (fun a ha => hT a (pSide_subset T p true ha))]
  have hmassR :
      ((∑ e ∈ T.offDiag, normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) =
        ((∑ e ∈ (pSide T p false).offDiag,
          normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) +
        ((∑ e ∈ (pSide T p true).offDiag,
          normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) := by
    exact_mod_cast hmass
  rw [hmassR]
  ring

/-- On either side, logged `p`-slack is exactly `BpOrdered`, independently
of which involution is used. -/
theorem log_mul_pSlack_pSide_eq_BpOrdered
    (T : Finset ℕ) (p : ℕ) (side : Bool)
    (hp : p.Prime) (hT : ∀ a ∈ T, 0 < a)
    (τ : pSide T p side → pSide T p side) :
    Real.log p * pSlack p (pSide T p side) τ =
      BpOrdered p (pSide T p side) := by
  rw [pSlack_pSide_eq_diffMass T p side hp hT τ]
  rw [mul_comm]
  exact diffMass_mul_log_eq_BpOrdered (pSide T p side) p hp
    (fun a ha => hT a (pSide_subset T p side ha))

/-- The full logged `p`-difference mass is recovered by the matching slacks
on the two deterministic sides. -/
theorem BpOrdered_eq_sum_pSide_slacks
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a)
    (τ0 : pSide T p false → pSide T p false)
    (τ1 : pSide T p true → pSide T p true) :
    BpOrdered p T =
      Real.log p * pSlack p (pSide T p false) τ0 +
        Real.log p * pSlack p (pSide T p true) τ1 := by
  rw [BpOrdered_pSide_partition T p hp hT,
    log_mul_pSlack_pSide_eq_BpOrdered T p false hp hT τ0,
    log_mul_pSlack_pSide_eq_BpOrdered T p true hp hT τ1]

end

end Erdos126
