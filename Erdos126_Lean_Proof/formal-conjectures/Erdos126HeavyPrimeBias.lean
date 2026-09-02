import Erdos126SideLabel
import Erdos126BiasGlobal
import Erdos126Padic

/-!
# Arithmetic components for the heavy-prime biased sample

The first positive normalized threshold partitions a positive finite set by
the exact `p`-adic valuation and by a pair of opposite unit residues modulo
`p` (modulo `4` when `p = 2`).  This file constructs those components as the
`PairedComponent`s required by `Erdos126.BiasGlobal`.
-/

open scoped BigOperators

namespace Erdos126.HeavyPrimeBias

open Erdos126.Padic Erdos126.BiasGlobal
open Erdos126.BiasedSample

noncomputable section

/-- Canonical name of the unordered pair `{r,-r}` at the first modulus. -/
def canonicalUnitResidue (p a : ℕ) : ℕ :=
  min (pUnit p a % sideModulus p) (sideModulus p - pUnit p a % sideModulus p)

/-- A root component is determined by an exact valuation stratum and an
unordered pair of opposite first-level unit residues. -/
def rootKey (p a : ℕ) : ℕ × ℕ :=
  (padicValNat p a, canonicalUnitResidue p a)

def rootIndices (T : Finset ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  T.attach.image fun a : T => rootKey p (a : ℕ)

def rootLeft (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) : Finset T :=
  Finset.univ.filter fun a => rootKey p a = i ∧ pUnitSide p a = false

def rootRight (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) : Finset T :=
  Finset.univ.filter fun a => rootKey p a = i ∧ pUnitSide p a = true

theorem canonicalUnitResidue_eq_of_modEq
    {p a b : ℕ} (hab : pUnit p a ≡ pUnit p b [MOD sideModulus p]) :
    canonicalUnitResidue p a = canonicalUnitResidue p b := by
  change pUnit p a % sideModulus p = pUnit p b % sideModulus p at hab
  simp only [canonicalUnitResidue, hab]

theorem canonicalUnitResidue_eq_of_dvd_add
    {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hab : sideModulus p ∣ pUnit p a + pUnit p b) :
    canonicalUnitResidue p a = canonicalUnitResidue p b := by
  let q := sideModulus p
  let r := pUnit p a % q
  let s := pUnit p b % q
  have hle : q ≤ r + s := by
    simpa only [q, r, s] using
      Nat.le_mod_add_mod_of_dvd_add_of_not_dvd hab
        (not_sideModulus_dvd_pUnit hp ha)
  have haddMod := Nat.add_mod_add_of_le_add_mod hle
  have hzero : (pUnit p a + pUnit p b) % q = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hab
  have hrs : r + s = q := by
    rw [hzero, zero_add] at haddMod
    simpa only [r, s] using haddMod.symm
  simp only [canonicalUnitResidue]
  have hqr : q - r = s := by omega
  have hqs : q - s = r := by omega
  rw [hqr, hqs, min_comm]

theorem rootKey_eq_of_normalisedSumVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hab : n ≤ normalisedSumVal p a b) :
    rootKey p a = rootKey p b := by
  have hres := (normalisedSumVal_threshold_iff hp ha hb hn).mp hab
  apply Prod.ext
  · exact hres.1
  · apply canonicalUnitResidue_eq_of_dvd_add hp ha
    exact (sideModulus_dvd_residueModulus hn).trans hres.2

theorem rootKey_eq_of_normalisedDiffVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (hn : 0 < n)
    (hab : n ≤ normalisedDiffVal p a b) :
    rootKey p a = rootKey p b := by
  have hres := (normalisedDiffVal_threshold_iff hp ha hb hne hn).mp hab
  apply Prod.ext
  · exact hres.1
  · apply canonicalUnitResidue_eq_of_modEq
    rw [modEq_iff_dvd_dist] at hres ⊢
    exact (sideModulus_dvd_residueModulus hn).trans hres.2

/-- Arithmetic side compatibility at every positive threshold: sum edges
cross the two root sides, while difference edges stay within one root side. -/
theorem root_compatibility_of_normalisedSumVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hab : n ≤ normalisedSumVal p a b) :
    rootKey p a = rootKey p b ∧ pUnitSide p a ≠ pUnitSide p b :=
  ⟨rootKey_eq_of_normalisedSumVal_threshold hp ha hb hn hab,
    pUnitSide_ne_of_normalisedSumVal_threshold hp ha hb hn hab⟩

theorem root_compatibility_of_normalisedDiffVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (hn : 0 < n)
    (hab : n ≤ normalisedDiffVal p a b) :
    rootKey p a = rootKey p b ∧ pUnitSide p a = pUnitSide p b :=
  ⟨rootKey_eq_of_normalisedDiffVal_threshold hp ha hb hne hn hab,
    pUnitSide_eq_of_normalisedDiffVal_threshold hp ha hb hne hn hab⟩

theorem rootLeft_disjoint_rootRight (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) :
    Disjoint (rootLeft T p i) (rootRight T p i) := by
  rw [Finset.disjoint_left]
  intro a haL haR
  have hL := (Finset.mem_filter.mp haL).2.2
  have hR := (Finset.mem_filter.mp haR).2.2
  simp_all

theorem rootLeft_side (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) :
    ∀ a ∈ rootLeft T p i, pUnitSide p a = false := by
  intro a ha
  exact (Finset.mem_filter.mp ha).2.2

theorem rootRight_side (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) :
    ∀ a ∈ rootRight T p i, pUnitSide p a = true := by
  intro a ha
  exact (Finset.mem_filter.mp ha).2.2

/-- The blocks indexed by distinct root keys are disjoint. -/
theorem rootBlocks_pairwiseDisjoint (T : Finset ℕ) (p : ℕ) :
    Set.PairwiseDisjoint (rootIndices T p : Set (ℕ × ℕ))
      fun i => rootLeft T p i ∪ rootRight T p i := by
  intro i hi j hj hij
  change Disjoint (rootLeft T p i ∪ rootRight T p i)
    (rootLeft T p j ∪ rootRight T p j)
  rw [Finset.disjoint_left]
  intro a hai haj
  have hki : rootKey p a = i := by
    rcases Finset.mem_union.mp hai with h | h
    · exact (Finset.mem_filter.mp h).2.1
    · exact (Finset.mem_filter.mp h).2.1
  have hkj : rootKey p a = j := by
    rcases Finset.mem_union.mp haj with h | h
    · exact (Finset.mem_filter.mp h).2.1
    · exact (Finset.mem_filter.mp h).2.1
  exact hij (hki.symm.trans hkj)

section MaximumMatching

variable {V : Type*} [DecidableEq V]

def leftAt (L R : Finset V) (k : Fin (min L.card R.card)) : L :=
  L.equivFin.symm ⟨k, lt_of_lt_of_le k.isLt (min_le_left _ _)⟩

def rightAt (L R : Finset V) (k : Fin (min L.card R.card)) : R :=
  R.equivFin.symm ⟨k, lt_of_lt_of_le k.isLt (min_le_right _ _)⟩

def maximumMatching (L R : Finset V) : Finset (V × V) :=
  Finset.univ.image fun k : Fin (min L.card R.card) =>
    ((leftAt L R k : V), (rightAt L R k : V))

theorem leftAt_injective (L R : Finset V) :
    Function.Injective (fun k : Fin (min L.card R.card) => (leftAt L R k : V)) := by
  intro k l h
  apply Fin.ext
  have hsub : leftAt L R k = leftAt L R l := Subtype.ext h
  have hfin := congrArg L.equivFin hsub
  have hcast :
      (⟨k, lt_of_lt_of_le k.isLt (min_le_left _ _)⟩ : Fin L.card) =
        ⟨l, lt_of_lt_of_le l.isLt (min_le_left _ _)⟩ := by
    simpa only [leftAt, Equiv.apply_symm_apply] using hfin
  exact congrArg (fun z : Fin L.card => z.val) hcast

theorem rightAt_injective (L R : Finset V) :
    Function.Injective (fun k : Fin (min L.card R.card) => (rightAt L R k : V)) := by
  intro k l h
  apply Fin.ext
  have hsub : rightAt L R k = rightAt L R l := Subtype.ext h
  have hfin := congrArg R.equivFin hsub
  have hcast :
      (⟨k, lt_of_lt_of_le k.isLt (min_le_right _ _)⟩ : Fin R.card) =
        ⟨l, lt_of_lt_of_le l.isLt (min_le_right _ _)⟩ := by
    simpa only [rightAt, Equiv.apply_symm_apply] using hfin
  exact congrArg (fun z : Fin R.card => z.val) hcast

theorem maximumMatching_mem (L R : Finset V) :
    ∀ e ∈ maximumMatching L R, e.1 ∈ L ∧ e.2 ∈ R := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
  exact ⟨(leftAt L R k).property, (rightAt L R k).property⟩

theorem maximumMatching_card (L R : Finset V) :
    (maximumMatching L R).card = min L.card R.card := by
  rw [maximumMatching, Finset.card_image_of_injective]
  · simp
  · intro k l h
    exact leftAt_injective L R (congrArg Prod.fst h)

theorem maximumMatching_fst_injective (L R : Finset V) :
    Set.InjOn Prod.fst (maximumMatching L R : Set (V × V)) := by
  intro e he f hf hef
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hf
  rw [Prod.mk.injEq]
  have hkl := leftAt_injective L R hef
  exact ⟨hef, congrArg (fun z => (rightAt L R z : V)) hkl⟩

theorem maximumMatching_snd_injective (L R : Finset V) :
    Set.InjOn Prod.snd (maximumMatching L R : Set (V × V)) := by
  intro e he f hf hef
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hf
  rw [Prod.mk.injEq]
  have hkl := rightAt_injective L R hef
  exact ⟨congrArg (fun z => (leftAt L R z : V)) hkl, hef⟩

end MaximumMatching

/-- The root arithmetic component, packaged for the finite biased sample. -/
def rootComponent (T : Finset ℕ) (p : ℕ) (i : ℕ × ℕ) :
    PairedComponent (fun a : T => pUnitSide p a) where
  left := rootLeft T p i
  right := rootRight T p i
  disjoint := rootLeft_disjoint_rootRight T p i
  left_side := rootLeft_side T p i
  right_side := rootRight_side T p i
  matching := maximumMatching (rootLeft T p i) (rootRight T p i)
  matching_mem := maximumMatching_mem _ _
  matching_card := maximumMatching_card _ _
  matching_fst_injective := maximumMatching_fst_injective _ _
  matching_snd_injective := maximumMatching_snd_injective _ _

/-- Direct instantiation of the global finite averaging theorem on the root
arithmetic components. -/
theorem one_eighth_rootWithinMass_le_expect_rootSlack
    (T : Finset ℕ) (p : ℕ) :
    1 / 8 * totalWithinMass (rootIndices T p)
        (fun a : T => pUnitSide p a) (rootComponent T p) ≤
      𝔼 omega : Erdos126.BiasedSample.SystemSample T,
        totalSlack (rootIndices T p)
          (fun a : T => pUnitSide p a) (rootComponent T p) omega := by
  exact one_eighth_totalWithinMass_le_expect_totalSlack
    (rootIndices T p) (fun a : T => pUnitSide p a)
    (rootComponent T p) (rootBlocks_pairwiseDisjoint T p)

section WeightedBridge

set_option maxHeartbeats 1000000

/-- Full normalized difference mass on attached ordered pairs. -/
def normalizedDiffMass (T : Finset ℕ) (p : ℕ) : ℚ :=
  ∑ e ∈ (Finset.univ : Finset T).offDiag,
    (normalisedDiffVal p e.1 e.2 : ℚ)

/-- Full normalized sum mass on attached ordered pairs. -/
def normalizedSumMass (T : Finset ℕ) (p : ℕ) : ℚ :=
  ∑ e ∈ (Finset.univ : Finset T).offDiag,
    (normalisedSumVal p e.1 e.2 : ℚ)

/-- Weighted endpoint mass of one involution.  Every nontrivial orbit occurs
twice, exactly as in `exists_involution_weighted`. -/
def normalizedMatchingMass (T : Finset ℕ) (p : ℕ) (τ : T → T) : ℚ :=
  ∑ a : T, if τ a ≠ a then (normalisedSumVal p a (τ a) : ℚ) else 0

def selectedNormalizedDiffMass (T : Finset ℕ) (p : ℕ)
    (omega : SystemSample T) : ℚ :=
  ∑ e ∈ (Finset.univ : Finset T).offDiag,
    (normalisedDiffVal p e.1 e.2 : ℚ) *
      pairIndicator (fun a : T => pUnitSide p a) omega e

def selectedNormalizedSumMass (T : Finset ℕ) (p : ℕ)
    (omega : SystemSample T) : ℚ :=
  ∑ e ∈ (Finset.univ : Finset T).offDiag,
    (normalisedSumVal p e.1 e.2 : ℚ) *
      pairIndicator (fun a : T => pUnitSide p a) omega e

def selectedNormalizedMatchingMass (T : Finset ℕ) (p : ℕ) (τ : T → T)
    (omega : SystemSample T) : ℚ :=
  ∑ a : T, (if τ a ≠ a then (normalisedSumVal p a (τ a) : ℚ) else 0) *
    pairIndicator (fun a : T => pUnitSide p a) omega (a, τ a)

/-- The random p-adic slack: retained difference mass plus the retained
matching correction, minus retained sum mass. -/
def selectedPadicSlack (T : Finset ℕ) (p : ℕ) (τ : T → T)
    (omega : SystemSample T) : ℚ :=
  selectedNormalizedDiffMass T p omega +
    selectedNormalizedMatchingMass T p τ omega -
      selectedNormalizedSumMass T p omega

theorem expect_selectedNormalizedDiffMass
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    (𝔼 omega : SystemSample T, selectedNormalizedDiffMass T p omega) =
      5 / 16 * normalizedDiffMass T p := by
  unfold selectedNormalizedDiffMass normalizedDiffMass
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.mul_expect]
  by_cases hd : normalisedDiffVal p e.1 e.2 = 0
  · simp [hd]
  have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
  have hneNat : (e.1 : ℕ) ≠ (e.2 : ℕ) := fun h => hne (Subtype.ext h)
  have hside := pUnitSide_eq_of_normalisedDiffVal_threshold hp
    (hT e.1 e.1.property) (hT e.2 e.2.property) hneNat (by omega)
    (show 1 ≤ normalisedDiffVal p e.1 e.2 by omega)
  have hE :
      (𝔼 omega : SystemSample T,
        pairIndicator (fun a : T => pUnitSide p a) omega e) = 5 / 16 := by
    unfold pairIndicator
    exact expect_system_sameSide_pair
      (side := fun a : T => pUnitSide p a) (u := e.1) (v := e.2) hne hside
  rw [hE]
  ring

theorem expect_selectedNormalizedSumMass
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    (𝔼 omega : SystemSample T, selectedNormalizedSumMass T p omega) =
      3 / 16 * normalizedSumMass T p := by
  unfold selectedNormalizedSumMass normalizedSumMass
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.mul_expect]
  by_cases hs : normalisedSumVal p e.1 e.2 = 0
  · simp [hs]
  have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
  have hside := pUnitSide_ne_of_normalisedSumVal_threshold hp
    (hT e.1 e.1.property) (hT e.2 e.2.property) (by omega)
    (show 1 ≤ normalisedSumVal p e.1 e.2 by omega)
  have hopp : pUnitSide p e.2 = !(pUnitSide p e.1) := by
    cases h1 : pUnitSide p e.1 <;> cases h2 : pUnitSide p e.2 <;> simp_all
  have hE :
      (𝔼 omega : SystemSample T,
        pairIndicator (fun a : T => pUnitSide p a) omega e) = 3 / 16 := by
    unfold pairIndicator
    exact expect_system_oppositeSide_pair
      (side := fun a : T => pUnitSide p a) (u := e.1) (v := e.2) hne hopp
  rw [hE]
  ring

theorem expect_selectedNormalizedMatchingMass
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) (τ : T → T) :
    (𝔼 omega : SystemSample T, selectedNormalizedMatchingMass T p τ omega) =
      3 / 16 * normalizedMatchingMass T p τ := by
  unfold selectedNormalizedMatchingMass normalizedMatchingMass
  rw [Finset.expect_sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_expect]
  by_cases hfix : τ a = a
  · simp [hfix]
  by_cases hs : normalisedSumVal p a (τ a) = 0
  · simp [hfix, hs]
  have hside := pUnitSide_ne_of_normalisedSumVal_threshold hp
    (hT a a.property) (hT (τ a) (τ a).property) (by omega)
    (show 1 ≤ normalisedSumVal p a (τ a) by omega)
  have hopp : pUnitSide p (τ a) = !(pUnitSide p a) := by
    cases h1 : pUnitSide p a <;> cases h2 : pUnitSide p (τ a) <;> simp_all
  have hE :
      (𝔼 omega : SystemSample T,
        pairIndicator (fun a : T => pUnitSide p a) omega (a, τ a)) = 3 / 16 := by
    unfold pairIndicator
    exact expect_system_oppositeSide_pair
      (side := fun x : T => pUnitSide p x) (u := a) (v := τ a)
        (fun h => hfix h.symm) hopp
  rw [hE]
  split <;> simp_all
  ring

/-- Attached version of the simultaneous weighted matching inequality. -/
theorem exists_attached_involution_weighted
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ τ : T → T, Function.Involutive τ ∧
      (∑ e ∈ (Finset.univ : Finset T).offDiag,
          normalisedSumVal p e.1 e.2) ≤
        (∑ e ∈ (Finset.univ : Finset T).offDiag,
          normalisedDiffVal p e.1 e.2) +
          ∑ a : T, if τ a ≠ a then normalisedSumVal p a (τ a) else 0 := by
  obtain ⟨τ, hτ, hthreshold⟩ := exists_involution_threshold T p hp hT
  refine ⟨τ, hτ, ?_⟩
  let m : T → ℕ := fun a =>
    if τ a ≠ a then normalisedSumVal p a (τ a) else 0
  have hlevels : ∀ t : ℕ,
      (((Finset.univ : Finset T).offDiag).filter fun e =>
        t + 1 ≤ normalisedSumVal p e.1 e.2).card ≤
      (((Finset.univ : Finset T).offDiag).filter fun e =>
        t + 1 ≤ normalisedDiffVal p e.1 e.2).card +
      1 * ((Finset.univ : Finset T).filter fun a => t + 1 ≤ m a).card := by
    intro t
    rw [card_attach_offDiag_filter T
      (fun a b => t + 1 ≤ normalisedSumVal p a b)]
    rw [card_attach_offDiag_filter T
      (fun a b => t + 1 ≤ normalisedDiffVal p a b)]
    have hfilter :
        ((Finset.univ : Finset T).filter fun a => t + 1 ≤ m a) =
          ((Finset.univ : Finset T).filter fun a =>
            τ a ≠ a ∧ t + 1 ≤ normalisedSumVal p a (τ a)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hne : τ a ≠ a
      · simp [m, hne]
      · have heq : τ a = a := not_ne_iff.mp hne
        simp [m, heq]
    rw [hfilter, one_mul]
    have hattach : T.attach = (Finset.univ : Finset T) := by
      ext a
      simp
    rw [← hattach]
    exact hthreshold t
  have hweighted := weighted_of_thresholds
    (Finset.univ : Finset T).offDiag (Finset.univ : Finset T).offDiag
    (Finset.univ : Finset T)
    (fun e => normalisedSumVal p e.1 e.2)
    (fun e => normalisedDiffVal p e.1 e.2) m 1 hlevels
  simpa only [m, one_mul] using hweighted

/-- The arithmetic-to-probability bridge for one prime.  One simultaneous
matching makes the expected selected p-adic slack at least one eighth of the
entire normalized p-difference valuation mass. -/
theorem exists_one_eighth_diffMass_le_expect_selectedPadicSlack
    (T : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hT : ∀ a ∈ T, 0 < a) :
    ∃ τ : T → T, Function.Involutive τ ∧
      1 / 8 * normalizedDiffMass T p ≤
        𝔼 omega : SystemSample T, selectedPadicSlack T p τ omega := by
  obtain ⟨τ, hτ, hweighted⟩ := exists_attached_involution_weighted T p hp hT
  refine ⟨τ, hτ, ?_⟩
  have hweightedQ : normalizedSumMass T p ≤
      normalizedDiffMass T p + normalizedMatchingMass T p τ := by
    unfold normalizedSumMass normalizedDiffMass normalizedMatchingMass
    exact_mod_cast hweighted
  unfold selectedPadicSlack
  rw [Finset.expect_sub_distrib,
    Finset.expect_add_distrib,
    expect_selectedNormalizedDiffMass T p hp hT,
    expect_selectedNormalizedMatchingMass T p hp hT τ,
    expect_selectedNormalizedSumMass T p hp hT]
  linarith

end WeightedBridge

end

end Erdos126.HeavyPrimeBias
