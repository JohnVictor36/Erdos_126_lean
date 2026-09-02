import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The local p-adic matching step for Erdős problem 126

This file isolates the finite combinatorial statement used in the proposed
square-root lower bound.  It is deliberately separate from the official
problem statement while the proof is being developed.

For an unordered pair `{a,b}`, `normalisedSumVal p a b` and
`normalisedDiffVal p a b` are the `p`-adic valuations after dividing both
`a+b` and `|a-b|` by `gcd(a,b)`, and also by `2` when `a` and `b` have the
same 2-adic valuation.  The definition below records the valuation directly;
this avoids formalising exact natural-number division at this stage.
-/

namespace Erdos126.Padic

open scoped BigOperators

section AbstractMatching

variable {V : Type*} [DecidableEq V]

/-- Contribution of one endpoint to the exponential matching score. -/
def matchingTerm (u : V → V → ℕ) (τ : V → V) (v : V) : ℕ :=
  if τ v = v then 0 else 4 ^ u v (τ v)

/-- The exponential score used to select one matching which is optimal at all
weight thresholds.  Every nontrivial two-cycle is counted at both endpoints.
Base `4` leaves ample room for the alternating repair: one new edge at level
`t` outweighs the loss of two edges of levels below `t`. -/
def matchingScore [Fintype V] (u : V → V → ℕ) (τ : V → V) : ℕ :=
  ∑ v, matchingTerm u τ v

/-- There is an involution of maximum exponential score. -/
theorem exists_matchingScore_maximizer [Fintype V] (u : V → V → ℕ) :
    ∃ τ : V → V, Function.Involutive τ ∧
      ∀ σ : V → V, Function.Involutive σ →
        matchingScore u σ ≤ matchingScore u τ := by
  classical
  let candidates := (Finset.univ : Finset (V → V)).filter Function.Involutive
  have hid : id ∈ candidates := by
    simp [candidates, Function.Involutive]
  obtain ⟨τ, hτ, hmax⟩ :=
    Finset.exists_max_image candidates (matchingScore u) ⟨id, hid⟩
  refine ⟨τ, (Finset.mem_filter.mp hτ).2, ?_⟩
  intro σ hσ
  exact hmax σ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩)

/-- Break the old edges incident with `a` and `b`, pair `a` with `b`, and
leave the abandoned partners fixed. -/
def repairInvolution (τ : V → V) (a b x : V) : V :=
  if x = a then b
  else if x = b then a
  else if x = τ a then τ a
  else if x = τ b then τ b
  else τ x

/-- The alternating repair is again an involution, provided `a` and `b` were
not already paired. -/
theorem repairInvolution_involutive
    {τ : V → V} (hτ : Function.Involutive τ) {a b : V}
    (hab : a ≠ b) (hpair : τ a ≠ b) :
    Function.Involutive (repairInvolution τ a b) := by
  classical
  have hτi : Function.Injective τ := hτ.injective
  have hpair' : τ b ≠ a := by
    intro h
    apply hpair
    rw [← hτ b, h]
  have hpartners : τ a ≠ τ b := hτi.ne hab
  have hτ_eq (v w : V) (h : τ v = w) : v = τ w := by
    rw [← hτ v, h]
  intro x
  grind [repairInvolution]

/-- Abstract component hypotheses at a fixed threshold.  They say that all
threshold edges meeting `L ∪ R` are exactly the edges of the complete
bipartite graph between `L` and `R`. -/
def IsThresholdComponent (u : V → V → ℕ) (t : ℕ)
    (L R : Finset V) : Prop :=
  Disjoint L R ∧
    (∀ a ∈ L, ∀ b ∈ R, t ≤ u a b) ∧
    (∀ a ∈ L, ∀ x, t ≤ u a x → x ∈ R) ∧
    (∀ b ∈ R, ∀ x, t ≤ u b x → x ∈ L)

/-- The numerical part of the alternating repair.  The old edges at `a` and
`b` have weights below `t`, while the new edge has weight at least `t`.
With base `4`, the two new endpoint contributions dominate the at most four
old endpoint contributions. -/
theorem matchingScore_lt_repair
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ v w, u v w = u w v)
    {τ : V → V} (hτ : Function.Involutive τ) {a b : V}
    (hab : a ≠ b) (hpair : τ a ≠ b) {t : ℕ} (ht : 0 < t)
    (ha : u a (τ a) < t) (hb : u b (τ b) < t)
    (habWeight : t ≤ u a b) :
    matchingScore u τ < matchingScore u (repairInvolution τ a b) := by
  classical
  let σ := repairInvolution τ a b
  let S : Finset V := {a, b, τ a, τ b}
  let C : Finset V := Finset.univ \ S
  let Q := 4 ^ (t - 1)
  have hτi : Function.Injective τ := hτ.injective
  have hpair' : τ b ≠ a := by
    intro h
    apply hpair
    rw [← hτ b, h]
  have hpartners : τ a ≠ τ b := hτi.ne hab
  have houtside :
      (∑ v ∈ C, matchingTerm u τ v) =
        ∑ v ∈ C, matchingTerm u σ v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : v ≠ a ∧ v ≠ b ∧ v ≠ τ a ∧ v ≠ τ b := by
      simpa only [C, S, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or] using hv
    have hσv : σ v = τ v := by
      simp only [σ, repairInvolution, if_neg hv'.1, if_neg hv'.2.1,
        if_neg hv'.2.2.1, if_neg hv'.2.2.2]
    simp only [matchingTerm, hσv]
  have hterm_le (v : V) (hv : u v (τ v) < t) :
      matchingTerm u τ v ≤ Q := by
    simp only [matchingTerm]
    split
    · exact Nat.zero_le _
    · exact Nat.pow_le_pow_right (by norm_num)
        (Nat.le_sub_one_of_lt hv)
  have hold (v : V) (hv : v ∈ S) : matchingTerm u τ v ≤ Q := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hterm_le _ ha
    · exact hterm_le _ hb
    · apply hterm_le
      simpa only [hτ a, hsymm (τ a) a] using ha
    · apply hterm_le
      simpa only [hτ b, hsymm (τ b) b] using hb
  have hcardS : S.card ≤ 4 := by
    simp only [S]
    grind [Finset.card_insert_le]
  have holdS : (∑ v ∈ S, matchingTerm u τ v) ≤ 4 * Q := by
    calc
      (∑ v ∈ S, matchingTerm u τ v) ≤ S.card • Q :=
        Finset.sum_le_card_nsmul S (matchingTerm u τ) Q hold
      _ = S.card * Q := by simp
      _ ≤ 4 * Q := Nat.mul_le_mul_right Q hcardS
  have hpow : 4 ^ t ≤ 4 ^ u a b :=
    Nat.pow_le_pow_right (by norm_num) habWeight
  have hσa : σ a = b := by
    simp [σ, repairInvolution]
  have hσb : σ b = a := by
    simp [σ, repairInvolution]
  have hnewa : matchingTerm u σ a = 4 ^ u a b := by
    simp [matchingTerm, hσa, hab.symm]
  have hnewb : matchingTerm u σ b = 4 ^ u a b := by
    simp [matchingTerm, hσb, hab, hsymm b a]
  have hpairSum :
      2 * 4 ^ t ≤ ∑ v ∈ ({a, b} : Finset V), matchingTerm u σ v := by
    rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    rw [hnewa, hnewb]
    omega
  have hpairSubset : ({a, b} : Finset V) ⊆ S := by
    simp [S]
  have hnewS : 2 * 4 ^ t ≤ ∑ v ∈ S, matchingTerm u σ v :=
    hpairSum.trans (Finset.sum_le_sum_of_subset hpairSubset)
  have hQpow : 4 * Q = 4 ^ t := by
    rw [show t = (t - 1) + 1 by omega, pow_succ]
    simp only [Q]
    omega
  have hspecial :
      (∑ v ∈ S, matchingTerm u τ v) <
        ∑ v ∈ S, matchingTerm u σ v := by
    have hpos : 0 < 4 ^ t := pow_pos (by norm_num) _
    apply lt_of_le_of_lt holdS
    apply lt_of_lt_of_le _ hnewS
    rw [hQpow]
    omega
  simp only [matchingScore]
  calc
    (∑ v, matchingTerm u τ v) =
        (∑ v ∈ C, matchingTerm u τ v) +
          ∑ v ∈ S, matchingTerm u τ v := by
      exact (Finset.sum_sdiff (f := matchingTerm u τ) (by simp : S ⊆ Finset.univ)).symm
    _ < (∑ v ∈ C, matchingTerm u τ v) +
          ∑ v ∈ S, matchingTerm u σ v :=
      Nat.add_lt_add_left hspecial _
    _ = (∑ v ∈ C, matchingTerm u σ v) +
          ∑ v ∈ S, matchingTerm u σ v := by rw [houtside]
    _ = ∑ v, matchingTerm u σ v :=
      Finset.sum_sdiff (f := matchingTerm u σ) (by simp : S ⊆ Finset.univ)

/-- The intended generic saturation statement.  A maximum-score involution
contains `min #L #R` threshold edges in every paired complete-bipartite
component.  Its proof is the four-vertex alternating repair above together
with the estimate
`4 * 4^(t-1) < 2 * 4^t` for `0 < t`.

This is kept as a separate theorem because it is the only generic
finite-matching fact still needed by the arithmetic residue decomposition. -/
theorem matchingScore_maximizer_saturates
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ a b, u a b = u b a)
    (τ : V → V) (hτ : Function.Involutive τ)
    (hmax : ∀ σ : V → V, Function.Involutive σ →
      matchingScore u σ ≤ matchingScore u τ)
    (t : ℕ) (ht : 0 < t) (L R : Finset V)
    (hcomp : IsThresholdComponent u t L R) :
    (L.filter fun a => t ≤ u a (τ a)).card = min L.card R.card := by
  classical
  let ML := L.filter fun a => t ≤ u a (τ a)
  let MR := R.filter fun b => t ≤ u b (τ b)
  have hmapLR : ∀ a ∈ ML, τ a ∈ MR := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨hcomp.2.2.1 a ha'.1 (τ a) ha'.2, ?_⟩
    simpa only [hτ a, hsymm (τ a) a] using ha'.2
  have hmapRL : ∀ b ∈ MR, τ b ∈ ML := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    apply Finset.mem_filter.mpr
    refine ⟨hcomp.2.2.2 b hb'.1 (τ b) hb'.2, ?_⟩
    simpa only [hτ b, hsymm (τ b) b] using hb'.2
  have hcards : ML.card = MR.card := by
    apply Finset.card_bij' (fun a _ => τ a) (fun b _ => τ b) hmapLR hmapRL
    · intro a ha
      exact hτ a
    · intro b hb
      exact hτ b
  have hupperL : ML.card ≤ L.card := Finset.card_filter_le _ _
  have hupperR : ML.card ≤ R.card := by
    rw [hcards]
    exact Finset.card_filter_le _ _
  apply le_antisymm (le_min hupperL hupperR)
  by_contra hnot
  have hlt : ML.card < min L.card R.card := Nat.lt_of_not_ge hnot
  have hltL : ML.card < L.card := lt_of_lt_of_le hlt (min_le_left _ _)
  have hltR : MR.card < R.card := by
    rw [← hcards]
    exact lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨a, haL, haML⟩ := Finset.exists_mem_notMem_of_card_lt_card hltL
  obtain ⟨b, hbR, hbMR⟩ := Finset.exists_mem_notMem_of_card_lt_card hltR
  have haLow : u a (τ a) < t := by
    have : ¬t ≤ u a (τ a) := by
      simpa only [ML, Finset.mem_filter, haL, true_and] using haML
    exact Nat.lt_of_not_ge this
  have hbLow : u b (τ b) < t := by
    have : ¬t ≤ u b (τ b) := by
      simpa only [MR, Finset.mem_filter, hbR, true_and] using hbMR
    exact Nat.lt_of_not_ge this
  have hab : a ≠ b := by
    exact fun h => (Finset.disjoint_left.mp hcomp.1 haL (h ▸ hbR))
  have hpair : τ a ≠ b := by
    intro h
    exact (Nat.not_le_of_lt haLow) (h ▸ hcomp.2.1 a haL b hbR)
  let σ := repairInvolution τ a b
  have hσ : Function.Involutive σ :=
    repairInvolution_involutive hτ hab hpair
  have hscore : matchingScore u τ < matchingScore u σ := by
    exact matchingScore_lt_repair u hsymm hτ hab hpair ht haLow hbLow
      (hcomp.2.1 a haL b hbR)
  exact (Nat.not_le_of_lt hscore) (hmax σ hσ)

/-- A maximum-score involution is a maximal matching at every positive
threshold: no threshold edge has both endpoints unmatched at that level. -/
theorem matchingScore_maximizer_threshold_maximal
    [Fintype V]
    (u : V → V → ℕ) (hsymm : ∀ a b, u a b = u b a)
    (τ : V → V) (hτ : Function.Involutive τ)
    (hmax : ∀ σ : V → V, Function.Involutive σ →
      matchingScore u σ ≤ matchingScore u τ)
    {n : ℕ} (hn : 0 < n) {a b : V} (hne : a ≠ b) (hab : n ≤ u a b) :
    n ≤ u a (τ a) ∨ n ≤ u b (τ b) := by
  by_contra h
  push_neg at h
  have hpair : τ a ≠ b := by
    intro heq
    exact (Nat.not_le_of_lt h.1) (heq ▸ hab)
  let σ := repairInvolution τ a b
  have hσ : Function.Involutive σ :=
    repairInvolution_involutive hτ hne hpair
  have hlt : matchingScore u τ < matchingScore u σ :=
    matchingScore_lt_repair u hsymm hτ hne hpair hn h.1 h.2 hab
  exact (Nat.not_le_of_lt hlt) (hmax σ hσ)

/-- Injection used to charge every non-matching threshold sum edge to a
threshold difference edge. -/
def thresholdRepairMap (u : V → V → ℕ) (τ : V → V) (n : ℕ)
    (e : V × V) : V × V :=
  if n ≤ u e.1 (τ e.1) then (e.2, τ e.1) else (τ e.2, e.1)

/-- Abstract global charging lemma.  The rectangle hypothesis says that two
threshold `u`-edges sharing an endpoint yield a threshold `d`-edge between
their other endpoints.  A maximal involutive matching then gives the exact
cardinality inequality needed in the p-adic argument, without enumerating
the residue components. -/
theorem threshold_card_le_difference_add_matching
    [Fintype V]
    (u d : V → V → ℕ) (hsymm : ∀ a b, u a b = u b a)
    (τ : V → V) (hτ : Function.Involutive τ)
    {n : ℕ} (hn : 0 < n)
    (hmaximal : ∀ {a b : V}, a ≠ b → n ≤ u a b →
      n ≤ u a (τ a) ∨ n ≤ u b (τ b))
    (hrectangle : ∀ {a b c : V}, b ≠ c →
      n ≤ u a b → n ≤ u a c → n ≤ d b c) :
    ((Finset.univ.offDiag).filter fun e => n ≤ u e.1 e.2).card ≤
      ((Finset.univ.offDiag).filter fun e => n ≤ d e.1 e.2).card +
        (Finset.univ.filter fun a => τ a ≠ a ∧ n ≤ u a (τ a)).card := by
  classical
  let E := (Finset.univ.offDiag).filter fun e => n ≤ u e.1 e.2
  let EM := E.filter fun e => τ e.1 = e.2
  let EU := E.filter fun e => τ e.1 ≠ e.2
  let D := (Finset.univ.offDiag).filter fun e => n ≤ d e.1 e.2
  let MV := Finset.univ.filter fun a => τ a ≠ a ∧ n ≤ u a (τ a)
  have hsplit : EM.card + EU.card = E.card := by
    exact Finset.card_filter_add_card_filter_not (s := E) (fun e => τ e.1 = e.2)
  have hmatch : EM.card = MV.card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      have hem := (Finset.mem_filter.mp he).2
      have heE := (Finset.mem_filter.mp he).1
      have heData := Finset.mem_filter.mp heE
      have hene := (Finset.mem_offDiag.mp heData.1).2.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro hfix
        apply hene
        rw [← hem, hfix]
      · simpa only [hem] using heData.2
    · intro e he f hf hfirst
      have heq := (Finset.mem_filter.mp he).2
      have hfq := (Finset.mem_filter.mp hf).2
      apply Prod.ext hfirst
      rw [← heq, ← hfq, hfirst]
    · intro a ha
      have haData := (Finset.mem_filter.mp ha).2
      refine ⟨(a, τ a), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, haData.1.symm⟩,
        haData.2⟩
  have hmap : Set.MapsTo (thresholdRepairMap u τ n) (↑EU : Set (V × V))
      (↑D : Set (V × V)) := by
    intro e he
    have heU := (Finset.mem_filter.mp he).1
    have heNot := (Finset.mem_filter.mp he).2
    have heData := Finset.mem_filter.mp heU
    have hene := (Finset.mem_offDiag.mp heData.1).2.2
    have hedge := heData.2
    by_cases ha : n ≤ u e.1 (τ e.1)
    · have htargetNe : e.2 ≠ τ e.1 := by exact fun h => heNot h.symm
      simp only [thresholdRepairMap, ha, ↓reduceIte]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, htargetNe⟩, ?_⟩
      exact hrectangle htargetNe hedge ha
    · have hb : n ≤ u e.2 (τ e.2) :=
        (hmaximal hene hedge).resolve_left ha
      have htargetNe : τ e.2 ≠ e.1 := by
        intro h
        apply heNot
        rw [← hτ e.2, h]
      simp only [thresholdRepairMap, ha, ↓reduceIte]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, htargetNe⟩, ?_⟩
      exact hrectangle htargetNe hb (by simpa only [hsymm e.2 e.1] using hedge)
  have hinj : Set.InjOn (thresholdRepairMap u τ n) (↑EU : Set (V × V)) := by
    intro e he f hf hmapEq
    have heNot := (Finset.mem_filter.mp he).2
    have hfNot := (Finset.mem_filter.mp hf).2
    by_cases heM : n ≤ u e.1 (τ e.1)
    · by_cases hfM : n ≤ u f.1 (τ f.1)
      · simp only [thresholdRepairMap, heM, hfM, ↓reduceIte] at hmapEq
        have h1 : e.1 = f.1 := hτ.injective (congrArg Prod.snd hmapEq)
        have h2 : e.2 = f.2 := congrArg Prod.fst hmapEq
        exact Prod.ext h1 h2
      · simp only [thresholdRepairMap, heM, hfM, ↓reduceIte] at hmapEq
        have hfirst : f.1 = τ e.1 := (congrArg Prod.snd hmapEq).symm
        exfalso
        apply hfM
        rw [hfirst, hτ e.1, hsymm (τ e.1) e.1]
        exact heM
    · by_cases hfM : n ≤ u f.1 (τ f.1)
      · simp only [thresholdRepairMap, heM, hfM, ↓reduceIte] at hmapEq
        have hfirst : e.1 = τ f.1 := congrArg Prod.snd hmapEq
        exfalso
        apply heM
        rw [hfirst, hτ f.1, hsymm (τ f.1) f.1]
        exact hfM
      · simp only [thresholdRepairMap, heM, hfM, ↓reduceIte] at hmapEq
        have h1 : e.1 = f.1 := congrArg Prod.snd hmapEq
        have h2 : e.2 = f.2 := hτ.injective (congrArg Prod.fst hmapEq)
        exact Prod.ext h1 h2
  have hunmatched : EU.card ≤ D.card :=
    Finset.card_le_card_of_injOn (thresholdRepairMap u τ n) hmap hinj
  change E.card ≤ D.card + MV.card
  omega

/-- Finite layer-cake identity for natural-valued weights. -/
theorem sum_card_threshold_eq_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℕ) (N : ℕ)
    (hN : ∀ x ∈ s, w x ≤ N) :
    (∑ t ∈ Finset.range N, (s.filter fun x => t + 1 ≤ w x).card) =
      ∑ x ∈ s, w x := by
  calc
    (∑ t ∈ Finset.range N, (s.filter fun x => t + 1 ≤ w x).card) =
        ∑ t ∈ Finset.range N, ∑ x ∈ s, if t + 1 ≤ w x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp
    _ = ∑ x ∈ s, ∑ t ∈ Finset.range N,
          if t + 1 ≤ w x then 1 else 0 := Finset.sum_comm
    _ = ∑ x ∈ s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxN := hN x hx
      have hfilter :
          (Finset.range N).filter (fun t => t + 1 ≤ w x) = Finset.range (w x) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [Finset.sum_boole, hfilter]
      simp

/-- Summing a cardinality inequality over all thresholds gives the
corresponding inequality for the total natural-valued weights. -/
theorem weighted_of_thresholds
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (u : α → ℕ) (d : β → ℕ) (m : γ → ℕ) (c : ℕ)
    (h : ∀ t : ℕ,
      (A.filter fun x => t + 1 ≤ u x).card ≤
        (B.filter fun x => t + 1 ≤ d x).card +
          c * (C.filter fun x => t + 1 ≤ m x).card) :
    (∑ x ∈ A, u x) ≤ (∑ x ∈ B, d x) + c * ∑ x ∈ C, m x := by
  let su := ∑ x ∈ A, u x
  let sd := ∑ x ∈ B, d x
  let sm := ∑ x ∈ C, m x
  let N := su + sd + sm
  have hu (x : α) (hx : x ∈ A) : u x ≤ N := by
    have hx' : u x ≤ su := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    simp only [N]
    omega
  have hd (x : β) (hx : x ∈ B) : d x ≤ N := by
    have hx' : d x ≤ sd := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    simp only [N]
    omega
  have hm (x : γ) (hx : x ∈ C) : m x ≤ N := by
    have hx' : m x ≤ sm := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    simp only [N]
    omega
  have huSum := sum_card_threshold_eq_sum A u N hu
  have hdSum := sum_card_threshold_eq_sum B d N hd
  have hmSum := sum_card_threshold_eq_sum C m N hm
  have hsum := Finset.sum_le_sum (s := Finset.range N) fun t ht => h t
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [huSum, hdSum, hmSum] at hsum
  exact hsum

end AbstractMatching

/-- The extra factor `2` in the common normaliser occurs exactly when the
two endpoints have equal 2-adic valuation. -/
def twoCorrection (a b : ℕ) : ℕ :=
  if padicValNat 2 a = padicValNat 2 b then 1 else 0

/-- The `p`-adic valuation of the common normaliser used for `a+b` and
`|a-b|`. -/
def normaliserVal (p a b : ℕ) : ℕ :=
  min (padicValNat p a) (padicValNat p b) +
    if p = 2 then twoCorrection a b else 0

/-- The `p`-adic valuation of the normalised sum attached to an edge. -/
def normalisedSumVal (p a b : ℕ) : ℕ :=
  padicValNat p (a + b) - normaliserVal p a b

/-- The `p`-adic valuation of the normalised absolute difference attached to
an edge. -/
def normalisedDiffVal (p a b : ℕ) : ℕ :=
  padicValNat p (a.dist b) - normaliserVal p a b

theorem normaliserVal_comm (p a b : ℕ) :
    normaliserVal p a b = normaliserVal p b a := by
  simp [normaliserVal, twoCorrection, min_comm, eq_comm]

theorem normalisedSumVal_comm (p a b : ℕ) :
    normalisedSumVal p a b = normalisedSumVal p b a := by
  simp [normalisedSumVal, add_comm, normaliserVal_comm]

theorem normalisedDiffVal_comm (p a b : ℕ) :
    normalisedDiffVal p a b = normalisedDiffVal p b a := by
  simp [normalisedDiffVal, Nat.dist_comm, normaliserVal_comm]

/-- The unit part obtained after removing the largest power of `p`. -/
def pUnit (p a : ℕ) : ℕ := a.divMaxPow p

theorem pow_val_mul_pUnit (p a : ℕ) :
    p ^ padicValNat p a * pUnit p a = a := by
  exact Nat.pow_padicValNat_mul_divMaxPow p a

theorem pUnit_pos {p a : ℕ} (ha : 0 < a) : 0 < pUnit p a := by
  have hfactor : 0 < p ^ padicValNat p a * pUnit p a := by
    rw [pow_val_mul_pUnit]
    exact ha
  exact Nat.pos_of_mul_pos_left hfactor

/-- Congruence modulo `q` is equivalently divisibility of the natural
absolute difference. -/
theorem modEq_iff_dvd_dist {q a b : ℕ} :
    a ≡ b [MOD q] ↔ q ∣ a.dist b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact Nat.modEq_iff_dvd' hab
  · rw [Nat.dist_eq_sub_of_le_right hba]
    constructor
    · intro h
      exact (Nat.modEq_iff_dvd' hba).mp h.symm
    · intro h
      exact ((Nat.modEq_iff_dvd' hba).mpr h).symm

/-- Once two positive numbers lie in the same valuation stratum, the
normalised valuation of their sum is just the valuation of the sum of their
unit parts (and is shifted down by one for `p = 2`). -/
theorem normalisedSumVal_eq_pUnit
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hab : padicValNat p a = padicValNat p b) :
    normalisedSumVal p a b =
      padicValNat p (pUnit p a + pUnit p b) - (if p = 2 then 1 else 0) := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := padicValNat p a
  have haFactor : p ^ s * pUnit p a = a := by
    exact pow_val_mul_pUnit p a
  have hbFactor : p ^ s * pUnit p b = b := by
    simpa only [s, hab] using pow_val_mul_pUnit p b
  have hpow : p ^ s ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hunitSum : pUnit p a + pUnit p b ≠ 0 := by
    exact Nat.ne_of_gt (Nat.add_pos_left (pUnit_pos ha) _)
  have hsum : a + b = p ^ s * (pUnit p a + pUnit p b) := by
    rw [mul_add, haFactor, hbFactor]
  have hval : padicValNat p (a + b) =
      s + padicValNat p (pUnit p a + pUnit p b) := by
    rw [hsum, padicValNat.mul hpow hunitSum, padicValNat.prime_pow]
  have hnormaliser : normaliserVal p a b =
      s + (if p = 2 then 1 else 0) := by
    by_cases htwo : p = 2
    · subst p
      simp [normaliserVal, twoCorrection, s, hab]
    · simp [normaliserVal, twoCorrection, s, htwo, ← hab]
  rw [normalisedSumVal, hval, hnormaliser, Nat.add_sub_add_left]

/-- The analogous unit-part formula for a non-diagonal difference. -/
theorem normalisedDiffVal_eq_pUnit
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hab : padicValNat p a = padicValNat p b) :
    normalisedDiffVal p a b =
      padicValNat p ((pUnit p a).dist (pUnit p b)) -
        (if p = 2 then 1 else 0) := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := padicValNat p a
  have haFactor : p ^ s * pUnit p a = a := by
    exact pow_val_mul_pUnit p a
  have hbFactor : p ^ s * pUnit p b = b := by
    simpa only [s, hab] using pow_val_mul_pUnit p b
  have hpow : p ^ s ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hunitNe : pUnit p a ≠ pUnit p b := by
    intro h
    apply hne
    rw [← haFactor, ← hbFactor, h]
  have hunitDist : (pUnit p a).dist (pUnit p b) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.dist_pos_of_ne hunitNe)
  have hdist : a.dist b = p ^ s * ((pUnit p a).dist (pUnit p b)) := by
    calc
      a.dist b = (p ^ s * pUnit p a).dist (p ^ s * pUnit p b) :=
        congrArg₂ Nat.dist haFactor.symm hbFactor.symm
      _ = p ^ s * ((pUnit p a).dist (pUnit p b)) := Nat.dist_mul_left _ _ _
  have hval : padicValNat p (a.dist b) =
      s + padicValNat p ((pUnit p a).dist (pUnit p b)) := by
    rw [hdist, padicValNat.mul hpow hunitDist, padicValNat.prime_pow]
  have hnormaliser : normaliserVal p a b =
      s + (if p = 2 then 1 else 0) := by
    by_cases htwo : p = 2
    · subst p
      simp [normaliserVal, twoCorrection, s, hab]
    · simp [normaliserVal, twoCorrection, s, htwo, ← hab]
  rw [normalisedDiffVal, hval, hnormaliser, Nat.add_sub_add_left]

/-- A positive normalised sum valuation can only join two vertices in the
same `p`-adic valuation stratum. -/
theorem eq_val_of_normalisedSumVal_pos
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hpos : 0 < normalisedSumVal p a b) :
    padicValNat p a = padicValNat p b := by
  letI : Fact p.Prime := ⟨hp⟩
  by_contra hab
  have hsumQ : (a : ℚ) + b ≠ 0 := by positivity
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have habZ : (padicValNat p a : ℤ) ≠ (padicValNat p b : ℤ) := by
    exact_mod_cast hab
  have hvalQ := padicValRat.add_eq_min (p := p) hsumQ haQ hbQ (by
    simpa only [padicValRat.of_nat] using habZ)
  rw [← Nat.cast_add] at hvalQ
  have hvalZ : (padicValNat p (a + b) : ℤ) =
      min (padicValNat p a : ℤ) (padicValNat p b : ℤ) := by
    simpa only [padicValRat.of_nat] using hvalQ
  have hval : padicValNat p (a + b) =
      min (padicValNat p a) (padicValNat p b) := by
    exact_mod_cast hvalZ
  have hzero : normalisedSumVal p a b = 0 := by
    simp [normalisedSumVal, normaliserVal, hval]
  omega

/-- The usual ultrametric equality for an absolute natural-number
difference, in the form needed below. -/
theorem padicValNat_dist_eq_min_of_ne_val
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hab : padicValNat p a ≠ padicValNat p b) :
    padicValNat p (a.dist b) =
      min (padicValNat p a) (padicValNat p b) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hne : a ≠ b := by
    intro h
    exact hab (congrArg (padicValNat p) h)
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have habZ : (padicValNat p a : ℤ) ≠ (padicValNat p b : ℤ) := by
    exact_mod_cast hab
  rcases le_total a b with hle | hle
  · have hlt : a < b := lt_of_le_of_ne hle hne
    have hcast : (b : ℚ) + -(a : ℚ) = ((b - a : ℕ) : ℚ) := by
      rw [Nat.cast_sub hle]
      ring
    have hsumQ : (b : ℚ) + -(a : ℚ) ≠ 0 := by
      rw [hcast]
      exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
    have hvalQ := padicValRat.add_eq_min (p := p) hsumQ hbQ
      (neg_ne_zero.mpr haQ) (by
        simpa only [padicValRat.of_nat, padicValRat.neg] using habZ.symm)
    rw [hcast] at hvalQ
    have hvalZ : (padicValNat p (b - a) : ℤ) =
        min (padicValNat p b : ℤ) (padicValNat p a : ℤ) := by
      simpa only [padicValRat.of_nat, padicValRat.neg] using hvalQ
    have hvalNat : padicValNat p (b - a) =
        min (padicValNat p b) (padicValNat p a) := by
      exact_mod_cast hvalZ
    rw [Nat.dist_eq_sub_of_le hle, hvalNat, min_comm]
  · have hlt : b < a := lt_of_le_of_ne hle hne.symm
    have hcast : (a : ℚ) + -(b : ℚ) = ((a - b : ℕ) : ℚ) := by
      rw [Nat.cast_sub hle]
      ring
    have hsumQ : (a : ℚ) + -(b : ℚ) ≠ 0 := by
      rw [hcast]
      exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt))
    have hvalQ := padicValRat.add_eq_min (p := p) hsumQ haQ
      (neg_ne_zero.mpr hbQ) (by
        simpa only [padicValRat.of_nat, padicValRat.neg] using habZ)
    rw [hcast] at hvalQ
    have hvalZ : (padicValNat p (a - b) : ℤ) =
        min (padicValNat p a : ℤ) (padicValNat p b : ℤ) := by
      simpa only [padicValRat.of_nat, padicValRat.neg] using hvalQ
    have hvalNat : padicValNat p (a - b) =
        min (padicValNat p a) (padicValNat p b) := by
      exact_mod_cast hvalZ
    rw [Nat.dist_eq_sub_of_le_right hle, hvalNat]

/-- A positive normalised difference valuation also stays within one
valuation stratum. -/
theorem eq_val_of_normalisedDiffVal_pos
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hpos : 0 < normalisedDiffVal p a b) :
    padicValNat p a = padicValNat p b := by
  by_contra hab
  have hval := padicValNat_dist_eq_min_of_ne_val hp ha hb hab
  have hzero : normalisedDiffVal p a b = 0 := by
    simp [normalisedDiffVal, normaliserVal, hval]
  omega

/-- Odd-prime residue description of a normalised sum threshold inside one
valuation stratum.  Thus the sum components are a residue class of unit
parts modulo `p^n` paired with its negative class. -/
theorem odd_normalisedSumVal_threshold_iff
    {p a b n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hb : 0 < b)
    (hab : padicValNat p a = padicValNat p b) :
    n ≤ normalisedSumVal p a b ↔
      p ^ n ∣ pUnit p a + pUnit p b := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [normalisedSumVal_eq_pUnit hp ha hb hab]
  simp only [hp2, ↓reduceIte, Nat.sub_zero]
  exact (padicValNat_dvd_iff_le
    (Nat.ne_of_gt (Nat.add_pos_left (pUnit_pos ha) _))).symm

/-- At `p = 2` the common normaliser removes one additional factor `2`, so
level `n > 0` is congruence modulo `2^(n+1)` on the odd unit parts. -/
theorem two_normalisedSumVal_threshold_iff
    {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : padicValNat 2 a = padicValNat 2 b) (hn : 0 < n) :
    n ≤ normalisedSumVal 2 a b ↔
      2 ^ (n + 1) ∣ pUnit 2 a + pUnit 2 b := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalisedSumVal_eq_pUnit Nat.prime_two ha hb hab]
  simp only [↓reduceIte]
  rw [padicValNat_dvd_iff_le
    (Nat.ne_of_gt (Nat.add_pos_left (pUnit_pos ha) _))]
  omega

/-- Odd-prime residue description of a normalised difference threshold.
Inside one valuation stratum these are the ordinary congruence classes of
unit parts modulo `p^n`. -/
theorem odd_normalisedDiffVal_threshold_iff
    {p a b n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hab : padicValNat p a = padicValNat p b) :
    n ≤ normalisedDiffVal p a b ↔
      p ^ n ∣ (pUnit p a).dist (pUnit p b) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hunitNe : pUnit p a ≠ pUnit p b := by
    intro h
    apply hne
    rw [← pow_val_mul_pUnit p a, ← pow_val_mul_pUnit p b, hab, h]
  rw [normalisedDiffVal_eq_pUnit hp ha hb hne hab]
  simp only [hp2, ↓reduceIte, Nat.sub_zero]
  exact (padicValNat_dvd_iff_le
    (Nat.ne_of_gt (Nat.dist_pos_of_ne hunitNe))).symm

/-- The `p = 2` difference classes use the same shifted modulus as the sum
classes. -/
theorem two_normalisedDiffVal_threshold_iff
    {a b n : ℕ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b)
    (hab : padicValNat 2 a = padicValNat 2 b) (hn : 0 < n) :
    n ≤ normalisedDiffVal 2 a b ↔
      2 ^ (n + 1) ∣ (pUnit 2 a).dist (pUnit 2 b) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hunitNe : pUnit 2 a ≠ pUnit 2 b := by
    intro h
    apply hne
    rw [← pow_val_mul_pUnit 2 a, ← pow_val_mul_pUnit 2 b, hab, h]
  rw [normalisedDiffVal_eq_pUnit Nat.prime_two ha hb hne hab]
  simp only [↓reduceIte]
  rw [padicValNat_dvd_iff_le
    (Nat.ne_of_gt (Nat.dist_pos_of_ne hunitNe))]
  omega

/-- Modulus governing the residue components at a positive normalised
threshold. -/
def residueModulus (p n : ℕ) : ℕ :=
  if p = 2 then 2 ^ (n + 1) else p ^ n

/-- A unit residue class and its negative class are distinct.  For odd `p`
this uses that `p` cannot divide both `2` and the unit part; for `p = 2`,
the shifted modulus leaves one power of `2` after cancellation. -/
theorem pUnit_not_same_and_opposite
    {p a u n : ℕ} (hp : p.Prime) (ha : 0 < a) (hn : 0 < n) :
    ¬(u ≡ pUnit p a [MOD residueModulus p n] ∧
      residueModulus p n ∣ u + pUnit p a) := by
  rintro ⟨hsame, hopp⟩
  have hsum0 : u + pUnit p a ≡ 0 [MOD residueModulus p n] :=
    Nat.modEq_zero_iff_dvd.mpr hopp
  have hto : u + pUnit p a ≡ pUnit p a + pUnit p a
      [MOD residueModulus p n] := hsame.add Nat.ModEq.rfl
  have haa0 : pUnit p a + pUnit p a ≡ 0 [MOD residueModulus p n] :=
    hto.symm.trans hsum0
  have hdiv : residueModulus p n ∣ pUnit p a + pUnit p a :=
    Nat.modEq_zero_iff_dvd.mp haa0
  have hunit : ¬p ∣ pUnit p a :=
    Nat.not_dvd_divMaxPow hp.one_lt (Nat.ne_of_gt ha)
  by_cases hp2 : p = 2
  · subst p
    have hcancel : 2 ^ n ∣ pUnit 2 a := by
      apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
      simpa only [residueModulus, ↓reduceIte, pow_succ, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc, two_mul] using hdiv
    have htwoPow : 2 ∣ 2 ^ n := dvd_pow_self 2 (Nat.ne_of_gt hn)
    exact hunit (htwoPow.trans hcancel)
  · have hpPow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hpSum : p ∣ pUnit p a + pUnit p a := by
      apply hpPow.trans
      simpa only [residueModulus, hp2, ↓reduceIte] using hdiv
    have hpProd : p ∣ 2 * pUnit p a := by
      simpa only [two_mul] using hpSum
    rcases hp.dvd_mul.mp hpProd with htwo | hunit'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
    · exact hunit hunit'

/-- Complete residue description, including the fact that all positive
threshold edges remain within one valuation stratum. -/
theorem normalisedSumVal_threshold_iff
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    n ≤ normalisedSumVal p a b ↔
      padicValNat p a = padicValNat p b ∧
        residueModulus p n ∣ pUnit p a + pUnit p b := by
  constructor
  · intro h
    have hpos : 0 < normalisedSumVal p a b := lt_of_lt_of_le hn h
    have hab := eq_val_of_normalisedSumVal_pos hp ha hb hpos
    refine ⟨hab, ?_⟩
    by_cases hp2 : p = 2
    · subst p
      simpa only [residueModulus, ↓reduceIte] using
        (two_normalisedSumVal_threshold_iff ha hb hab hn).mp h
    · simpa only [residueModulus, hp2, ↓reduceIte] using
        (odd_normalisedSumVal_threshold_iff hp hp2 ha hb hab).mp h
  · rintro ⟨hab, hdiv⟩
    by_cases hp2 : p = 2
    · subst p
      apply (two_normalisedSumVal_threshold_iff ha hb hab hn).mpr
      simpa only [residueModulus, ↓reduceIte] using hdiv
    · apply (odd_normalisedSumVal_threshold_iff hp hp2 ha hb hab).mpr
      simpa only [residueModulus, hp2, ↓reduceIte] using hdiv

/-- Difference version of the complete residue description, for an
off-diagonal pair. -/
theorem normalisedDiffVal_threshold_iff
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (hn : 0 < n) :
    n ≤ normalisedDiffVal p a b ↔
      padicValNat p a = padicValNat p b ∧
        (pUnit p a ≡ pUnit p b [MOD residueModulus p n]) := by
  constructor
  · intro h
    have hpos : 0 < normalisedDiffVal p a b := lt_of_lt_of_le hn h
    have hab := eq_val_of_normalisedDiffVal_pos hp ha hb hpos
    refine ⟨hab, ?_⟩
    rw [modEq_iff_dvd_dist]
    by_cases hp2 : p = 2
    · subst p
      simpa only [residueModulus, ↓reduceIte] using
        (two_normalisedDiffVal_threshold_iff ha hb hne hab hn).mp h
    · simpa only [residueModulus, hp2, ↓reduceIte] using
        (odd_normalisedDiffVal_threshold_iff hp hp2 ha hb hne hab).mp h
  · rintro ⟨hab, hmod⟩
    rw [modEq_iff_dvd_dist] at hmod
    by_cases hp2 : p = 2
    · subst p
      apply (two_normalisedDiffVal_threshold_iff ha hb hne hab hn).mpr
      simpa only [residueModulus, ↓reduceIte] using hmod
    · apply (odd_normalisedDiffVal_threshold_iff hp hp2 ha hb hne hab).mpr
      simpa only [residueModulus, hp2, ↓reduceIte] using hmod

/-- The same-residue side of the component containing `a`. -/
def sameResidueClass (T : Finset ℕ) (p n : ℕ) (a : T) : Finset T :=
  Finset.univ.filter fun x =>
    padicValNat p x = padicValNat p a ∧
      (pUnit p x ≡ pUnit p a [MOD residueModulus p n])

/-- The opposite-residue side paired with `sameResidueClass`. -/
def oppositeResidueClass (T : Finset ℕ) (p n : ℕ) (a : T) : Finset T :=
  Finset.univ.filter fun x =>
    padicValNat p x = padicValNat p a ∧
      residueModulus p n ∣ pUnit p x + pUnit p a

theorem mem_sameResidueClass_iff
    {T : Finset ℕ} {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hT : ∀ x ∈ T, 0 < x) {a x : T} (hne : x ≠ a) :
    x ∈ sameResidueClass T p n a ↔
      n ≤ normalisedDiffVal p x a := by
  have hnatNe : (x : ℕ) ≠ (a : ℕ) := fun h => hne (Subtype.ext h)
  simpa only [sameResidueClass, Finset.mem_filter, Finset.mem_univ, true_and] using
    (normalisedDiffVal_threshold_iff hp (hT x x.property) (hT a a.property)
      hnatNe hn).symm

theorem mem_oppositeResidueClass_iff
    {T : Finset ℕ} {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hT : ∀ x ∈ T, 0 < x) {a x : T} :
    x ∈ oppositeResidueClass T p n a ↔
      n ≤ normalisedSumVal p x a := by
  simpa only [oppositeResidueClass, Finset.mem_filter, Finset.mem_univ, true_and]
    using (normalisedSumVal_threshold_iff hp (hT x x.property) (hT a a.property) hn).symm

/-- At every positive threshold, the normalised sum graph is a disjoint
union of complete bipartite graphs between a residue class and its negative.
This is the arithmetic wrapper required by
`matchingScore_maximizer_saturates`; it handles odd primes and `p = 2`
uniformly through `residueModulus`. -/
theorem normalisedSumVal_isThresholdComponent
    (T : Finset ℕ) (p n : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hT : ∀ x ∈ T, 0 < x) (a : T) :
    IsThresholdComponent
      (fun x y : T => normalisedSumVal p x y) n
      (sameResidueClass T p n a) (oppositeResidueClass T p n a) := by
  classical
  have hpos (x : T) : 0 < (x : ℕ) := hT x x.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxSame hxOpp
    have hs := (Finset.mem_filter.mp hxSame).2
    have ho := (Finset.mem_filter.mp hxOpp).2
    exact pUnit_not_same_and_opposite hp (hpos a) hn ⟨hs.2, ho.2⟩
  · intro x hx y hy
    have hs := (Finset.mem_filter.mp hx).2
    have ho := (Finset.mem_filter.mp hy).2
    apply (normalisedSumVal_threshold_iff hp (hpos x) (hpos y) hn).mpr
    refine ⟨hs.1.trans ho.1.symm, ?_⟩
    have hsameAdd : pUnit p x + pUnit p y ≡
        pUnit p a + pUnit p y [MOD residueModulus p n] :=
      hs.2.add Nat.ModEq.rfl
    have htoOpp : pUnit p x + pUnit p y ≡
        pUnit p y + pUnit p a [MOD residueModulus p n] := by
      simpa only [add_comm] using hsameAdd
    have hoppZero : pUnit p y + pUnit p a ≡ 0
        [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr ho.2
    exact Nat.modEq_zero_iff_dvd.mp (htoOpp.trans hoppZero)
  · intro x hx y hxy
    have hs := (Finset.mem_filter.mp hx).2
    have he := (normalisedSumVal_threshold_iff hp (hpos x) (hpos y) hn).mp hxy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, he.1.symm.trans hs.1, ?_⟩
    have hedgeZero : pUnit p x + pUnit p y ≡ 0
        [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr he.2
    have hsameAdd : pUnit p x + pUnit p y ≡
        pUnit p a + pUnit p y [MOD residueModulus p n] :=
      hs.2.add Nat.ModEq.rfl
    have hanchorZero : pUnit p a + pUnit p y ≡ 0
        [MOD residueModulus p n] := hsameAdd.symm.trans hedgeZero
    apply Nat.modEq_zero_iff_dvd.mp
    simpa only [add_comm] using hanchorZero
  · intro y hy x hyx
    have ho := (Finset.mem_filter.mp hy).2
    have he := (normalisedSumVal_threshold_iff hp (hpos y) (hpos x) hn).mp hyx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, he.1.symm.trans ho.1, ?_⟩
    have hoppZero : pUnit p y + pUnit p a ≡ 0
        [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr ho.2
    have hedgeZero : pUnit p y + pUnit p x ≡ 0
        [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr he.2
    have hsumEq : pUnit p y + pUnit p x ≡
        pUnit p y + pUnit p a [MOD residueModulus p n] :=
      hedgeZero.trans hoppZero.symm
    exact Nat.ModEq.add_left_cancel' (pUnit p y) hsumEq

/-- Two positive-level normalised sum edges with a common endpoint force a
normalised difference edge between the other endpoints. -/
theorem normalisedSumVal_rectangle
    {p a b c n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) (hne : b ≠ c)
    (hab : n ≤ normalisedSumVal p a b)
    (hac : n ≤ normalisedSumVal p a c) :
    n ≤ normalisedDiffVal p b c := by
  have hab' := (normalisedSumVal_threshold_iff hp ha hb hn).mp hab
  have hac' := (normalisedSumVal_threshold_iff hp ha hc hn).mp hac
  apply (normalisedDiffVal_threshold_iff hp hb hc hne hn).mpr
  refine ⟨hab'.1.symm.trans hac'.1, ?_⟩
  have habZero : pUnit p a + pUnit p b ≡ 0
      [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr hab'.2
  have hacZero : pUnit p a + pUnit p c ≡ 0
      [MOD residueModulus p n] := Nat.modEq_zero_iff_dvd.mpr hac'.2
  have hsumEq : pUnit p a + pUnit p b ≡ pUnit p a + pUnit p c
      [MOD residueModulus p n] := habZero.trans hacZero.symm
  exact Nat.ModEq.add_left_cancel' (pUnit p a) hsumEq

/-- Passing from pairs of attached elements back to pairs in the original
finset preserves the cardinality of every edge predicate. -/
theorem card_attach_offDiag_filter
    (T : Finset ℕ) (P : ℕ → ℕ → Prop) [DecidableRel P] :
    (((Finset.univ : Finset T).offDiag).filter fun e => P e.1 e.2).card =
      (T.offDiag.filter fun e => P e.1 e.2).card := by
  classical
  apply Finset.card_bij (fun e _ => ((e.1 : ℕ), (e.2 : ℕ)))
  · intro e he
    have heData := Finset.mem_filter.mp he
    have heOff := Finset.mem_offDiag.mp heData.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_offDiag.mpr
      ⟨e.1.property, e.2.property, fun h => heOff.2.2 (Subtype.ext h)⟩, heData.2⟩
  · intro e he f hf h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  · intro e he
    have heData := Finset.mem_filter.mp he
    have heOff := Finset.mem_offDiag.mp heData.1
    let a : T := ⟨e.1, heOff.1⟩
    let b : T := ⟨e.2, heOff.2.1⟩
    refine ⟨(a, b), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩, heData.2⟩
    intro h
    exact heOff.2.2 (congrArg Subtype.val h)

/-- A finset of canonically oriented edges is an undirected matching in `T`.
The long last clause says that distinct edges have disjoint endpoints. -/
def IsMatching (T : Finset ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M, e.1 ∈ T ∧ e.2 ∈ T ∧ e.1 < e.2) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

/-- A partial matching can equivalently be encoded by an involution on the
finite vertex type.  Fixed points are unmatched vertices; every other orbit
has two elements and is a matched edge.  This is usually the most convenient
form for later sums over vertices. -/
def IsPartialMatching {T : Finset ℕ} (τ : T → T) : Prop :=
  Function.Involutive τ

/-- Involution version of the simultaneous threshold theorem.  The last
cardinality counts both endpoints of every retained matching edge, so it is
exactly twice the number of matching edges at that threshold. -/
theorem exists_involution_threshold
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ τ : T → T, IsPartialMatching τ ∧
      ∀ t : ℕ,
        (T.offDiag.filter fun e => t + 1 ≤ normalisedSumVal p e.1 e.2).card ≤
          (T.offDiag.filter fun e => t + 1 ≤ normalisedDiffVal p e.1 e.2).card +
            (T.attach.filter fun a =>
              τ a ≠ a ∧ t + 1 ≤ normalisedSumVal p a (τ a)).card := by
  classical
  let u : T → T → ℕ := fun a b => normalisedSumVal p a b
  let d : T → T → ℕ := fun a b => normalisedDiffVal p a b
  have hsymm : ∀ a b, u a b = u b a := by
    intro a b
    exact normalisedSumVal_comm p a b
  obtain ⟨τ, hτ, hmax⟩ := exists_matchingScore_maximizer u
  refine ⟨τ, hτ, ?_⟩
  intro t
  let n := t + 1
  have hn : 0 < n := by omega
  have hmaximal : ∀ {a b : T}, a ≠ b → n ≤ u a b →
      n ≤ u a (τ a) ∨ n ≤ u b (τ b) := by
    intro a b hne hab
    exact matchingScore_maximizer_threshold_maximal u hsymm τ hτ hmax hn hne hab
  have hrectangle : ∀ {a b c : T}, b ≠ c →
      n ≤ u a b → n ≤ u a c → n ≤ d b c := by
    intro a b c hne hab hac
    have hneNat : (b : ℕ) ≠ (c : ℕ) := fun h => hne (Subtype.ext h)
    exact normalisedSumVal_rectangle hp (hT a a.property) (hT b b.property)
      (hT c c.property) hn hneNat hab hac
  have hcard := threshold_card_le_difference_add_matching
    u d hsymm τ hτ hn hmaximal hrectangle
  dsimp only [u, d] at hcard
  rw [card_attach_offDiag_filter T
      (fun a b => n ≤ normalisedSumVal p a b),
    card_attach_offDiag_filter T
      (fun a b => n ≤ normalisedDiffVal p a b)] at hcard
  have hattach : T.attach = (Finset.univ : Finset T) := by
    ext a
    simp
  simpa only [n, hattach] using hcard

/-- Weighted involution form obtained by summing
`exists_involution_threshold` over all positive valuation thresholds. -/
theorem exists_involution_weighted
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ τ : T → T, IsPartialMatching τ ∧
      (∑ e ∈ T.offDiag, normalisedSumVal p e.1 e.2) ≤
        (∑ e ∈ T.offDiag, normalisedDiffVal p e.1 e.2) +
          ∑ a ∈ T.attach,
            if τ a ≠ a then normalisedSumVal p a (τ a) else 0 := by
  classical
  obtain ⟨τ, hτ, hthreshold⟩ := exists_involution_threshold T p hp hT
  refine ⟨τ, hτ, ?_⟩
  let m : T → ℕ := fun a =>
    if τ a ≠ a then normalisedSumVal p a (τ a) else 0
  have hlevels : ∀ t : ℕ,
      (T.offDiag.filter fun e => t + 1 ≤ normalisedSumVal p e.1 e.2).card ≤
        (T.offDiag.filter fun e => t + 1 ≤ normalisedDiffVal p e.1 e.2).card +
          1 * (T.attach.filter fun a => t + 1 ≤ m a).card := by
    intro t
    have hfilter :
        (T.attach.filter fun a => t + 1 ≤ m a) =
          (T.attach.filter fun a =>
            τ a ≠ a ∧ t + 1 ≤ normalisedSumVal p a (τ a)) := by
      ext a
      simp only [Finset.mem_filter]
      by_cases h : τ a ≠ a
      · simp [m, h]
      · have heq : τ a = a := not_ne_iff.mp h
        simp [m, h, heq]
    rw [hfilter, one_mul]
    exact hthreshold t
  have hweighted := weighted_of_thresholds T.offDiag T.offDiag T.attach
    (fun e => normalisedSumVal p e.1 e.2)
    (fun e => normalisedDiffVal p e.1 e.2) m 1 hlevels
  simpa only [m, one_mul] using hweighted

/-- Orient each nontrivial orbit of an involution by the ambient order on
natural numbers.  Every two-cycle then occurs exactly once. -/
def matchingOfInvolution {T : Finset ℕ} (τ : T → T) : Finset (ℕ × ℕ) :=
  Finset.image (fun a : T => ((a : ℕ), (τ a : ℕ)))
    (T.attach.filter fun a : T => (a : ℕ) < (τ a : ℕ))

/-- The canonical edges of an involution form an undirected matching. -/
theorem matchingOfInvolution_isMatching {T : Finset ℕ} (τ : T → T)
    (hτ : Function.Involutive τ) : IsMatching T (matchingOfInvolution τ) := by
  classical
  constructor
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have halt := (Finset.mem_filter.mp ha).2
    exact ⟨a.property, (τ a).property, halt⟩
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    have halt := (Finset.mem_filter.mp ha).2
    have hblt := (Finset.mem_filter.mp hb).2
    have hτi : Function.Injective τ := hτ.injective
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hab
      apply hef
      have : a = b := Subtype.ext hab
      subst b
      rfl
    · intro hab
      have hab' : a = τ b := Subtype.ext hab
      have hback : (τ b : ℕ) < (b : ℕ) := by
        simpa only [hab', hτ b] using halt
      exact Nat.lt_asymm hblt hback
    · intro hab
      have hab' : τ a = b := Subtype.ext hab
      have hback : (τ a : ℕ) < (a : ℕ) := by
        simpa only [← hab', hτ a] using hblt
      exact Nat.lt_asymm halt hback
    · intro hab
      apply hef
      have : a = b := hτi (Subtype.ext hab)
      subst b
      rfl

/-- At a symmetric weight threshold, active endpoints of an involution
inject into two labelled copies of its canonically oriented active edges. -/
theorem card_activeVertices_le_two_mul_activeMatching
    {T : Finset ℕ} (τ : T → T) (hτ : Function.Involutive τ)
    (w : ℕ → ℕ → ℕ) (hsymm : ∀ a b, w a b = w b a) (q : ℕ) :
    (T.attach.filter fun a => τ a ≠ a ∧ q ≤ w a (τ a)).card ≤
      2 * ((matchingOfInvolution τ).filter fun e => q ≤ w e.1 e.2).card := by
  classical
  let S := T.attach.filter fun a => τ a ≠ a ∧ q ≤ w a (τ a)
  let E := (matchingOfInvolution τ).filter fun e => q ≤ w e.1 e.2
  let orient : T → Bool × (ℕ × ℕ) := fun a =>
    if (a : ℕ) < (τ a : ℕ) then
      (false, ((a : ℕ), (τ a : ℕ)))
    else
      (true, ((τ a : ℕ), (a : ℕ)))
  have hmaps : Set.MapsTo orient (↑S : Set T)
      (↑((Finset.univ : Finset Bool) ×ˢ E) : Set (Bool × (ℕ × ℕ))) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    change orient a ∈ (Finset.univ : Finset Bool) ×ˢ E
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [orient]
    split_ifs with halt
    · apply Finset.mem_filter.mpr
      refine ⟨?_, ha'.2.2⟩
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, halt⟩, rfl⟩
    · have hneVal : (τ a : ℕ) ≠ (a : ℕ) := by
        intro h
        exact ha'.2.1 (Subtype.ext h)
      have hback : (τ a : ℕ) < (a : ℕ) :=
        lt_of_le_of_ne (Nat.le_of_not_gt halt) hneVal
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        refine ⟨τ a, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩, ?_⟩
        · simpa only [hτ a] using hback
        · simp only [hτ a]
      · simpa only [hsymm (τ a) a] using ha'.2.2
  have hinj : Set.InjOn orient (↑S : Set T) := by
    intro a ha b hb hab
    by_cases halt : (a : ℕ) < (τ a : ℕ)
    · by_cases hblt : (b : ℕ) < (τ b : ℕ)
      · have hval := congrArg (fun z : Bool × (ℕ × ℕ) => z.2.1) hab
        simp only [orient, if_pos halt, if_pos hblt] at hval
        exact Subtype.ext hval
      · have hlabel := congrArg (fun z : Bool × (ℕ × ℕ) => z.1) hab
        simp only [orient, if_pos halt, if_neg hblt] at hlabel
        contradiction
    · by_cases hblt : (b : ℕ) < (τ b : ℕ)
      · have hlabel := congrArg (fun z : Bool × (ℕ × ℕ) => z.1) hab
        simp only [orient, if_neg halt, if_pos hblt] at hlabel
        contradiction
      · have hval := congrArg (fun z : Bool × (ℕ × ℕ) => z.2.2) hab
        simp only [orient, if_neg halt, if_neg hblt] at hval
        exact Subtype.ext hval
  have hcard := Finset.card_le_card_of_injOn orient hmaps hinj
  simpa only [S, E, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Nat.reduceMul] using hcard

/-- Ordered pairs in a complementary pair of residue classes contribute
`2*x*y` sum-edges.  Deleting a maximum matching removes `2*min x y` of
them.  The two same-class difference cliques contribute
`x*(x-1)+y*(y-1)` ordered edges. -/
theorem local_residue_count (x y : ℕ) :
    (2 : ℤ) * ((x : ℤ) * y - min x y) ≤
      (x : ℤ) * (x - 1) + (y : ℤ) * (y - 1) := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]
    by_cases h : x = y
    · subst y
      ring_nf
      exact le_rfl
    · have hlt : x < y := lt_of_le_of_ne hxy h
      have hgap' : (x : ℤ) + 1 ≤ y := by
        exact_mod_cast hlt
      have hgap : (1 : ℤ) ≤ (y : ℤ) - x := by
        linarith
      have hprod : 0 ≤ ((y : ℤ) - x) * ((y : ℤ) - x - 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  · rw [min_eq_right (le_of_not_ge hxy)]
    have hyx : y < x := lt_of_not_ge hxy
    have hgap' : (y : ℤ) + 1 ≤ x := by
      exact_mod_cast hyx
    have hgap : (1 : ℤ) ≤ (x : ℤ) - y := by
      linarith
    have hprod : 0 ≤ ((x : ℤ) - y) * ((x : ℤ) - y - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Threshold form of the simultaneous matching lemma.  One matching must
work for every power `p^t`, not a separately chosen matching at each level.

The proof is a finite refinement argument.  At a fixed valuation stratum,
residue classes modulo successive powers of `p` form a rooted tree.  A class
and its negative form a bipartite component.  First match maximally in every
child component, then match the unused vertices arbitrarily inside the
parent component.  Refining from the deepest nonempty level upwards preserves
maximality at all earlier levels.  The local estimate is
`local_residue_count`.
-/
theorem exists_matching_threshold
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ M : Finset (ℕ × ℕ), IsMatching T M ∧
      ∀ t : ℕ,
        (T.offDiag.filter fun e => t + 1 ≤ normalisedSumVal p e.1 e.2).card ≤
          (T.offDiag.filter fun e => t + 1 ≤ normalisedDiffVal p e.1 e.2).card +
            2 * (M.filter fun e => t + 1 ≤ normalisedSumVal p e.1 e.2).card := by
  obtain ⟨τ, hτ, hthreshold⟩ := exists_involution_threshold T p hp hT
  refine ⟨matchingOfInvolution τ, matchingOfInvolution_isMatching τ hτ, ?_⟩
  intro t
  exact (hthreshold t).trans <| Nat.add_le_add_left
    (card_activeVertices_le_two_mul_activeMatching τ hτ
      (normalisedSumVal p) (normalisedSumVal_comm p) (t + 1)) _

/-- Weighted form of `exists_matching_threshold`.  Because `offDiag` contains
both orientations of each unordered edge, a matched edge is counted twice on
the right. -/
theorem exists_matching_weighted
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ M : Finset (ℕ × ℕ), IsMatching T M ∧
      (∑ e ∈ T.offDiag, normalisedSumVal p e.1 e.2) ≤
        (∑ e ∈ T.offDiag, normalisedDiffVal p e.1 e.2) +
          2 * ∑ e ∈ M, normalisedSumVal p e.1 e.2 := by
  obtain ⟨M, hM, hthreshold⟩ := exists_matching_threshold T p hp hT
  refine ⟨M, hM, ?_⟩
  exact weighted_of_thresholds T.offDiag T.offDiag M
    (fun e => normalisedSumVal p e.1 e.2)
    (fun e => normalisedDiffVal p e.1 e.2)
    (fun e => normalisedSumVal p e.1 e.2) 2 hthreshold

end Erdos126.Padic
