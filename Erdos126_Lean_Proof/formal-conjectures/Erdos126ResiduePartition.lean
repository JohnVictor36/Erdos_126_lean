import Erdos126Padic

/-!
# Counting a partition into opposite residue classes

This file contains the finite counting bridge between the local residue-class
picture and the threshold inequality used in `exists_involution_threshold`.
It is deliberately abstract: `L i` and `R i` are the two sides of one
complete bipartite component of the sum graph, while their two off-diagonal
cliques are the corresponding pieces of the difference graph.
-/

namespace Erdos126.Padic

open scoped BigOperators

section ResiduePartition

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- The ordered edges between two disjoint sides of one component. -/
def orderedCrossEdges (L R : Finset V) : Finset (V × V) :=
  L ×ˢ R ∪ R ×ˢ L

/-- The ordered, non-loop edges within the two sides of one component. -/
def orderedWithinEdges (L R : Finset V) : Finset (V × V) :=
  L.offDiag ∪ R.offDiag

/-- Vertices whose involution edge survives at the given threshold. -/
def matchedThresholdVertices (u : V → V → ℕ) (τ : V → V) (t : ℕ)
    (S : Finset V) : Finset V :=
  S.filter fun v => t ≤ u v (τ v)

theorem card_orderedCrossEdges {L R : Finset V} (hLR : Disjoint L R) :
    (orderedCrossEdges L R).card = 2 * L.card * R.card := by
  rw [orderedCrossEdges, Finset.card_union_of_disjoint]
  · simp only [Finset.card_product]
    ring
  · exact Finset.disjoint_product.mpr (Or.inl hLR)

theorem card_orderedWithinEdges {L R : Finset V} (hLR : Disjoint L R) :
    (orderedWithinEdges L R).card =
      L.card * (L.card - 1) + R.card * (R.card - 1) := by
  rw [orderedWithinEdges, Finset.card_union_of_disjoint]
  · rw [Finset.offDiag_card, Finset.offDiag_card]
    simp only [Nat.mul_sub_one]
  · rw [Finset.disjoint_left]
    intro e heL heR
    have heL' := Finset.mem_offDiag.mp heL
    have heR' := Finset.mem_offDiag.mp heR
    exact (Finset.disjoint_left.mp hLR heL'.1) heR'.1

/-- Natural-number form of the local residue count.  The two complete
bipartite orientations are bounded by the two within-side cliques together
with the endpoints of a maximum matching. -/
theorem local_residue_count_nat (x y : ℕ) :
    2 * x * y ≤ x * (x - 1) + y * (y - 1) + 2 * min x y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
  have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy
  have h := local_residue_count x y
  push_cast [Nat.cast_sub hx1, Nat.cast_sub hy1] at h
  rw [← Nat.cast_min] at h
  exact_mod_cast (show (2 : ℤ) * x * y ≤
      (x : ℤ) * (x - 1) + (y : ℤ) * (y - 1) + 2 * min x y by
    linarith)

/-- Swapping the two sides preserves the threshold-component property when
the weight is symmetric. -/
theorem IsThresholdComponent.swap
    {u : V → V → ℕ} (hsymm : ∀ v w, u v w = u w v)
    {t : ℕ} {L R : Finset V} (hcomp : IsThresholdComponent u t L R) :
    IsThresholdComponent u t R L := by
  refine ⟨hcomp.1.symm, ?_, hcomp.2.2.2, hcomp.2.2.1⟩
  intro b hb a ha
  rw [hsymm]
  exact hcomp.2.1 a ha b hb

/-- A maximum-score involution has twice `min #L #R` threshold endpoints in
one complete bipartite threshold component. -/
theorem card_matchedThresholdVertices_component
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ v w, u v w = u w v)
    (τ : V → V) (hτ : Function.Involutive τ)
    (hmax : ∀ σ : V → V, Function.Involutive σ →
      matchingScore u σ ≤ matchingScore u τ)
    (t : ℕ) (ht : 0 < t) (L R : Finset V)
    (hcomp : IsThresholdComponent u t L R) :
    (matchedThresholdVertices u τ t (L ∪ R)).card =
      2 * min L.card R.card := by
  have hL := matchingScore_maximizer_saturates
    u hsymm τ hτ hmax t ht L R hcomp
  have hR := matchingScore_maximizer_saturates
    u hsymm τ hτ hmax t ht R L (hcomp.swap hsymm)
  have hfilter :
      matchedThresholdVertices u τ t (L ∪ R) =
        matchedThresholdVertices u τ t L ∪
          matchedThresholdVertices u τ t R := by
    ext v
    simp [matchedThresholdVertices, or_and_right]
  rw [hfilter, Finset.card_union_of_disjoint]
  · simp only [matchedThresholdVertices] at hL hR ⊢
    rw [hL, hR, min_comm]
    omega
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    have hvL' := (Finset.mem_filter.mp hvL).1
    have hvR' := (Finset.mem_filter.mp hvR).1
    exact (Finset.disjoint_left.mp hcomp.1 hvL') hvR'

/-- Edge families supported on pairwise disjoint vertex blocks are themselves
pairwise disjoint.  Only the first endpoint is needed to certify this. -/
theorem orderedCrossEdges_pairwiseDisjoint
    (I : Finset ι) (L R : ι → Finset V)
    (hparts : (↑I : Set ι).PairwiseDisjoint fun i => L i ∪ R i) :
    (↑I : Set ι).PairwiseDisjoint fun i => orderedCrossEdges (L i) (R i) := by
  intro i hi j hj hij
  change Disjoint (orderedCrossEdges (L i) (R i))
    (orderedCrossEdges (L j) (R j))
  rw [Finset.disjoint_left]
  intro e hei hej
  have hei' : e.1 ∈ L i ∪ R i := by
    rcases Finset.mem_union.mp hei with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mp h).1
    · exact Finset.mem_union_right _ (Finset.mem_product.mp h).1
  have hej' : e.1 ∈ L j ∪ R j := by
    rcases Finset.mem_union.mp hej with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mp h).1
    · exact Finset.mem_union_right _ (Finset.mem_product.mp h).1
  exact (Finset.disjoint_left.mp (hparts hi hj hij) hei') hej'

theorem orderedWithinEdges_pairwiseDisjoint
    (I : Finset ι) (L R : ι → Finset V)
    (hparts : (↑I : Set ι).PairwiseDisjoint fun i => L i ∪ R i) :
    (↑I : Set ι).PairwiseDisjoint fun i => orderedWithinEdges (L i) (R i) := by
  intro i hi j hj hij
  change Disjoint (orderedWithinEdges (L i) (R i))
    (orderedWithinEdges (L j) (R j))
  rw [Finset.disjoint_left]
  intro e hei hej
  have hei' : e.1 ∈ L i ∪ R i := by
    rcases Finset.mem_union.mp hei with h | h
    · exact Finset.mem_union_left _ (Finset.mem_offDiag.mp h).1
    · exact Finset.mem_union_right _ (Finset.mem_offDiag.mp h).1
  have hej' : e.1 ∈ L j ∪ R j := by
    rcases Finset.mem_union.mp hej with h | h
    · exact Finset.mem_union_left _ (Finset.mem_offDiag.mp h).1
    · exact Finset.mem_union_right _ (Finset.mem_offDiag.mp h).1
  exact (Finset.disjoint_left.mp (hparts hi hj hij) hei') hej'

theorem matchedThresholdVertices_pairwiseDisjoint
    (u : V → V → ℕ) (τ : V → V) (t : ℕ)
    (I : Finset ι) (L R : ι → Finset V)
    (hparts : (↑I : Set ι).PairwiseDisjoint fun i => L i ∪ R i) :
    (↑I : Set ι).PairwiseDisjoint fun i =>
      matchedThresholdVertices u τ t (L i ∪ R i) := by
  exact hparts.mono fun i v hv => (Finset.mem_filter.mp hv).1

/-- Global ordered-edge count for a partition into complete bipartite
threshold components.  This is the purely finite bridge: the sum threshold
edges are at most the difference threshold edges plus the threshold endpoints
of one maximum-score involution. -/
theorem threshold_card_inequality_of_residue_partition
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ v w, u v w = u w v)
    (τ : V → V) (hτ : Function.Involutive τ)
    (hmax : ∀ σ : V → V, Function.Involutive σ →
      matchingScore u σ ≤ matchingScore u τ)
    (t : ℕ) (ht : 0 < t)
    (I : Finset ι) (L R : ι → Finset V)
    (hparts : (↑I : Set ι).PairwiseDisjoint fun i => L i ∪ R i)
    (hcomp : ∀ i ∈ I, IsThresholdComponent u t (L i) (R i)) :
    (I.biUnion fun i => orderedCrossEdges (L i) (R i)).card ≤
      (I.biUnion fun i => orderedWithinEdges (L i) (R i)).card +
        (I.biUnion fun i =>
          matchedThresholdVertices u τ t (L i ∪ R i)).card := by
  rw [Finset.card_biUnion (orderedCrossEdges_pairwiseDisjoint I L R hparts)]
  rw [Finset.card_biUnion (orderedWithinEdges_pairwiseDisjoint I L R hparts)]
  rw [Finset.card_biUnion
    (matchedThresholdVertices_pairwiseDisjoint u τ t I L R hparts)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [card_orderedCrossEdges (hcomp i hi).1]
  rw [card_orderedWithinEdges (hcomp i hi).1]
  rw [card_matchedThresholdVertices_component
    u hsymm τ hτ hmax t ht (L i) (R i) (hcomp i hi)]
  exact local_residue_count_nat (L i).card (R i).card

/-- Wrapper for the actual threshold finsets.  Arithmetic residue lemmas are
used only to identify the sum threshold graph with the cross-edge union and
to embed the within-edge union in the difference threshold graph. -/
theorem threshold_card_inequality_of_identification
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ v w, u v w = u w v)
    (τ : V → V) (hτ : Function.Involutive τ)
    (hmax : ∀ σ : V → V, Function.Involutive σ →
      matchingScore u σ ≤ matchingScore u τ)
    (t : ℕ) (ht : 0 < t)
    (I : Finset ι) (L R : ι → Finset V)
    (hparts : (↑I : Set ι).PairwiseDisjoint fun i => L i ∪ R i)
    (hcomp : ∀ i ∈ I, IsThresholdComponent u t (L i) (R i))
    (sumEdges diffEdges : Finset (V × V)) (matchedVertices : Finset V)
    (hsum : sumEdges = I.biUnion fun i => orderedCrossEdges (L i) (R i))
    (hdiff : (I.biUnion fun i => orderedWithinEdges (L i) (R i)) ⊆ diffEdges)
    (hmatched : (I.biUnion fun i =>
      matchedThresholdVertices u τ t (L i ∪ R i)) ⊆ matchedVertices) :
    sumEdges.card ≤ diffEdges.card + matchedVertices.card := by
  rw [hsum]
  calc
    (I.biUnion fun i => orderedCrossEdges (L i) (R i)).card ≤
        (I.biUnion fun i => orderedWithinEdges (L i) (R i)).card +
          (I.biUnion fun i =>
            matchedThresholdVertices u τ t (L i ∪ R i)).card :=
      threshold_card_inequality_of_residue_partition
        u hsymm τ hτ hmax t ht I L R hparts hcomp
    _ ≤ diffEdges.card + matchedVertices.card :=
      Nat.add_le_add (Finset.card_le_card hdiff) (Finset.card_le_card hmatched)

end ResiduePartition

end Erdos126.Padic
