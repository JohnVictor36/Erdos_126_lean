import Erdos126Potentials
import Erdos126BiasGlobal
import Erdos126RealGoodEvent

/-!
# Reindexing a selected subtype as a finset of natural numbers

The biased experiment selects a `Finset T`, where `T : Finset ℕ` is viewed as
its attached subtype.  The arithmetic potentials, on the other hand, are
stated for finsets of natural numbers.  This file gives the lossless
reindexing between those two representations.  In particular, cardinalities,
off-diagonal sums, positivity, and all ordered logarithmic potentials are
preserved exactly.
-/

namespace Erdos126.SelectionBridge

open scoped BigOperators
open BiasedSample BiasGlobal
open RealGoodEvent

noncomputable section

/-- Forget the membership proof on a selected finset of the attached subtype. -/
def selectedNat {T : Finset ℕ} (S : Finset T) : Finset ℕ :=
  S.image fun a : T => (a : ℕ)

theorem subtypeVal_injective {T : Finset ℕ} :
    Function.Injective (fun a : T => (a : ℕ)) := by
  intro a b hab
  exact Subtype.ext hab

@[simp]
theorem mem_selectedNat {T : Finset ℕ} {S : Finset T} {a : ℕ} :
    a ∈ selectedNat S ↔ ∃ ha : a ∈ T, (⟨a, ha⟩ : T) ∈ S := by
  constructor
  · intro ha
    obtain ⟨x, hxS, hxa⟩ := Finset.mem_image.mp ha
    subst a
    exact ⟨x.property, by simpa using hxS⟩
  · rintro ⟨haT, haS⟩
    exact Finset.mem_image.mpr ⟨⟨a, haT⟩, haS, rfl⟩

theorem selectedNat_subset {T : Finset ℕ} (S : Finset T) :
    selectedNat S ⊆ T := by
  intro a ha
  exact (mem_selectedNat.mp ha).choose

@[simp]
theorem selectedNat_univ (T : Finset ℕ) :
    selectedNat (Finset.univ : Finset T) = T := by
  ext a
  simp only [mem_selectedNat, Finset.mem_univ]
  constructor
  · rintro ⟨ha, _⟩
    exact ha
  · intro ha
    exact ⟨ha, trivial⟩

@[simp]
theorem card_selectedNat {T : Finset ℕ} (S : Finset T) :
    (selectedNat S).card = S.card := by
  exact Finset.card_image_of_injective S subtypeVal_injective

theorem selectedNat_nonempty_iff {T : Finset ℕ} (S : Finset T) :
    (selectedNat S).Nonempty ↔ S.Nonempty := by
  rw [← Finset.card_pos, ← Finset.card_pos, card_selectedNat]

theorem selectedNat_pos {T : Finset ℕ} (S : Finset T)
    (hT : ∀ a ∈ T, 0 < a) :
    ∀ a ∈ selectedNat S, 0 < a := by
  intro a ha
  exact hT a (selectedNat_subset S ha)

@[simp]
theorem card_selectedNat_selectedSet
    {T : Finset ℕ} (side : T → Bool) (omega : SystemSample T) :
    (selectedNat (selectedSet side omega)).card =
      (selectedSet side omega).card :=
  card_selectedNat _

/-- The rational good-size condition gives the integral inequality used in
the denominator of the metric estimate. -/
theorem card_le_eight_mul_selectedNat_card_of_good
    {T : Finset ℕ} (side : T → Bool) (omega : SystemSample T)
    (hgood : GoodEvent.Good side T.card omega) :
    T.card ≤ 8 * (selectedNat (selectedSet side omega)).card := by
  rw [card_selectedNat_selectedSet]
  unfold GoodEvent.Good at hgood
  have hq : (T.card : ℚ) ≤ 8 * ((selectedSet side omega).card : ℚ) := by
    linarith
  exact_mod_cast hq

@[simp]
theorem pairIndicator_eq_selected_ite
    {V : Type*} [Fintype V] [LinearOrder V]
    (side : V → Bool) (omega : SystemSample V) (e : V × V) :
    pairIndicator side omega e =
      if e.1 ∈ selectedSet side omega ∧ e.2 ∈ selectedSet side omega
      then 1 else 0 := by
  simp only [pairIndicator, selectedSet, Finset.mem_filter, Finset.mem_univ,
    true_and, retainedIndicator]
  by_cases h1 : retained omega.orientation (side e.1) (omega.label e.1) <;>
    by_cases h2 : retained omega.orientation (side e.2) (omega.label e.2) <;>
    simp [h1, h2]

/-- Multiplication by the pair indicator is exactly restriction to the
selected off-diagonal edges. -/
theorem sum_selectedSet_offDiag_eq_indicator
    {V : Type*} [Fintype V] [LinearOrder V]
    (side : V → Bool) (omega : SystemSample V) (f : V × V → ℚ) :
    (∑ e ∈ (selectedSet side omega).offDiag, f e) =
      ∑ e ∈ (Finset.univ : Finset V).offDiag,
        f e * pairIndicator side omega e := by
  let g : V × V → ℚ := fun e => f e * pairIndicator side omega e
  calc
    (∑ e ∈ (selectedSet side omega).offDiag, f e) =
        ∑ e ∈ (selectedSet side omega).offDiag, g e := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_offDiag.mp he
      dsimp only [g]
      rw [pairIndicator_eq_selected_ite]
      simp [he'.1, he'.2.1]
    _ = ∑ e ∈ (Finset.univ : Finset V).offDiag, g e := by
      apply Finset.sum_subset
      · intro e he
        have he' := Finset.mem_offDiag.mp he
        exact Finset.mem_offDiag.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _, he'.2.2⟩
      · intro e heUniv heSelected
        have he' := Finset.mem_offDiag.mp heUniv
        dsimp only [g]
        rw [pairIndicator_eq_selected_ite]
        have hnot : ¬(e.1 ∈ selectedSet side omega ∧
            e.2 ∈ selectedSet side omega) := by
          intro hboth
          exact heSelected
            (Finset.mem_offDiag.mpr ⟨hboth.1, hboth.2, he'.2.2⟩)
        simp [hnot]

/-- Real-valued form of exact restriction to the selected edges. -/
theorem sum_selectedSet_offDiag_eq_realIndicator
    {V : Type*} [Fintype V] [LinearOrder V]
    (side : V → Bool) (omega : SystemSample V) (f : V × V → ℝ) :
    (∑ e ∈ (selectedSet side omega).offDiag, f e) =
      ∑ e ∈ (Finset.univ : Finset V).offDiag,
        f e * realPairIndicator side omega e := by
  let g : V × V → ℝ := fun e => f e * realPairIndicator side omega e
  calc
    (∑ e ∈ (selectedSet side omega).offDiag, f e) =
        ∑ e ∈ (selectedSet side omega).offDiag, g e := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := Finset.mem_offDiag.mp he
      dsimp only [g, realPairIndicator]
      rw [pairIndicator_eq_selected_ite]
      simp [he'.1, he'.2.1]
    _ = ∑ e ∈ (Finset.univ : Finset V).offDiag, g e := by
      apply Finset.sum_subset
      · intro e he
        have he' := Finset.mem_offDiag.mp he
        exact Finset.mem_offDiag.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _, he'.2.2⟩
      · intro e heUniv heSelected
        have he' := Finset.mem_offDiag.mp heUniv
        dsimp only [g, realPairIndicator]
        rw [pairIndicator_eq_selected_ite]
        have hnot : ¬(e.1 ∈ selectedSet side omega ∧
            e.2 ∈ selectedSet side omega) := by
          intro hboth
          exact heSelected
            (Finset.mem_offDiag.mpr ⟨hboth.1, hboth.2, he'.2.2⟩)
        simp [hnot]

/-- The coordinatewise coercion from subtype edges to natural-number edges. -/
def edgeVal {T : Finset ℕ} (e : T × T) : ℕ × ℕ :=
  ((e.1 : ℕ), (e.2 : ℕ))

theorem edgeVal_injective {T : Finset ℕ} :
    Function.Injective (edgeVal (T := T)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [edgeVal, Prod.mk.injEq] at h
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

/-- Off-diagonal edges commute exactly with forgetting subtype proofs. -/
theorem selectedNat_offDiag {T : Finset ℕ} (S : Finset T) :
    (selectedNat S).offDiag = S.offDiag.image (edgeVal (T := T)) := by
  ext e
  constructor
  · intro he
    have he' := Finset.mem_offDiag.mp he
    obtain ⟨haT, haS⟩ := mem_selectedNat.mp he'.1
    obtain ⟨hbT, hbS⟩ := mem_selectedNat.mp he'.2.1
    let a : T := ⟨e.1, haT⟩
    let b : T := ⟨e.2, hbT⟩
    have hab : a ≠ b := by
      intro h
      apply he'.2.2
      exact congrArg Subtype.val h
    apply Finset.mem_image.mpr
    refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨haS, hbS, hab⟩, ?_⟩
    rfl
  · intro he
    obtain ⟨e', he'S, he'e⟩ := Finset.mem_image.mp he
    subst e
    have he' := Finset.mem_offDiag.mp he'S
    apply Finset.mem_offDiag.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨e'.1, he'.1, rfl⟩
    · exact Finset.mem_image.mpr ⟨e'.2, he'.2.1, rfl⟩
    · intro h
      apply he'.2.2
      exact Subtype.ext h

/-- Generic reindexing of an off-diagonal sum. -/
theorem sum_selectedNat_offDiag_eq
    {T : Finset ℕ} (S : Finset T) {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) :
    (∑ e ∈ (selectedNat S).offDiag, f e) =
      ∑ e ∈ S.offDiag, f (edgeVal e) := by
  rw [selectedNat_offDiag S]
  exact Finset.sum_image fun _ _ _ _ h => edgeVal_injective h

/-- Reindexing the full attached subtype does not change an off-diagonal
natural-number edge sum. -/
theorem sum_attach_offDiag_eq
    (T : Finset ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ × ℕ → M) :
    (∑ e ∈ (Finset.univ : Finset T).offDiag, f (edgeVal e)) =
      ∑ e ∈ T.offDiag, f e := by
  rw [← sum_selectedNat_offDiag_eq (Finset.univ : Finset T) f,
    selectedNat_univ]

theorem sum_selectedNat_normalisedSumVal_eq
    {T : Finset ℕ} (S : Finset T) (p : ℕ) :
    (∑ e ∈ (selectedNat S).offDiag,
        Padic.normalisedSumVal p e.1 e.2) =
      ∑ e ∈ S.offDiag, Padic.normalisedSumVal p e.1 e.2 := by
  simpa only [edgeVal] using
    sum_selectedNat_offDiag_eq S
      (fun e : ℕ × ℕ => Padic.normalisedSumVal p e.1 e.2)

theorem sum_selectedNat_normalisedDiffVal_eq
    {T : Finset ℕ} (S : Finset T) (p : ℕ) :
    (∑ e ∈ (selectedNat S).offDiag,
        Padic.normalisedDiffVal p e.1 e.2) =
      ∑ e ∈ S.offDiag, Padic.normalisedDiffVal p e.1 e.2 := by
  simpa only [edgeVal] using
    sum_selectedNat_offDiag_eq S
      (fun e : ℕ × ℕ => Padic.normalisedDiffVal p e.1 e.2)

theorem AweightOrdered_selectedNat
    {T : Finset ℕ} (S : Finset T) :
    AweightOrdered (selectedNat S) =
      ∑ e ∈ S.offDiag,
        Real.log (Normalized.normalizedSum e.1 e.2) := by
  rw [AweightOrdered]
  simpa only [edgeVal] using
    sum_selectedNat_offDiag_eq S
      (fun e : ℕ × ℕ => Real.log (Normalized.normalizedSum e.1 e.2))

theorem BweightOrdered_selectedNat
    {T : Finset ℕ} (S : Finset T) :
    BweightOrdered (selectedNat S) =
      ∑ e ∈ S.offDiag,
        Real.log (Normalized.normalizedDist e.1 e.2) := by
  rw [BweightOrdered]
  simpa only [edgeVal] using
    sum_selectedNat_offDiag_eq S
      (fun e : ℕ × ℕ => Real.log (Normalized.normalizedDist e.1 e.2))

theorem BpOrdered_selectedNat
    {T : Finset ℕ} (S : Finset T) (p : ℕ) :
    BpOrdered p (selectedNat S) =
      ∑ e ∈ S.offDiag,
        (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
          Real.log p := by
  rw [BpOrdered]
  simpa only [edgeVal] using
    sum_selectedNat_offDiag_eq S
      (fun e : ℕ × ℕ =>
        (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) * Real.log p)

theorem BPOrdered_selectedNat
    {T : Finset ℕ} (S : Finset T) (P : Finset ℕ) :
    BPOrdered P (selectedNat S) =
      ∑ p ∈ P, ∑ e ∈ S.offDiag,
        (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) *
          Real.log p := by
  rw [BPOrdered]
  apply Finset.sum_congr rfl
  intro p hp
  exact BpOrdered_selectedNat S p

/-- The selected normalized-sum logarithmic potential, expressed directly in
the full sample with its real zero-one pair indicator. -/
theorem AweightOrdered_selectedSet
    (T : Finset ℕ) (side : T → Bool) (omega : SystemSample T) :
    AweightOrdered (selectedNat (selectedSet side omega)) =
      ∑ e ∈ (Finset.univ : Finset T).offDiag,
        Real.log (Normalized.normalizedSum e.1 e.2) *
          realPairIndicator side omega e := by
  rw [AweightOrdered_selectedNat]
  exact sum_selectedSet_offDiag_eq_realIndicator side omega
    (fun e : T × T => Real.log (Normalized.normalizedSum e.1 e.2))

theorem BweightOrdered_selectedSet
    (T : Finset ℕ) (side : T → Bool) (omega : SystemSample T) :
    BweightOrdered (selectedNat (selectedSet side omega)) =
      ∑ e ∈ (Finset.univ : Finset T).offDiag,
        Real.log (Normalized.normalizedDist e.1 e.2) *
          realPairIndicator side omega e := by
  rw [BweightOrdered_selectedNat]
  exact sum_selectedSet_offDiag_eq_realIndicator side omega
    (fun e : T × T => Real.log (Normalized.normalizedDist e.1 e.2))

theorem BpOrdered_selectedSet
    (T : Finset ℕ) (side : T → Bool) (omega : SystemSample T) (p : ℕ) :
    BpOrdered p (selectedNat (selectedSet side omega)) =
      ∑ e ∈ (Finset.univ : Finset T).offDiag,
        ((padicValNat p (Normalized.normalizedDist e.1 e.2) : ℕ) : ℝ) *
          Real.log p * realPairIndicator side omega e := by
  rw [BpOrdered_selectedNat]
  exact sum_selectedSet_offDiag_eq_realIndicator side omega
    (fun e : T × T =>
      ((padicValNat p (Normalized.normalizedDist e.1 e.2) : ℕ) : ℝ) *
        Real.log p)

theorem BPOrdered_selectedSet
    (T : Finset ℕ) (side : T → Bool) (omega : SystemSample T)
    (P : Finset ℕ) :
    BPOrdered P (selectedNat (selectedSet side omega)) =
      ∑ p ∈ P, ∑ e ∈ (Finset.univ : Finset T).offDiag,
        ((padicValNat p (Normalized.normalizedDist e.1 e.2) : ℕ) : ℝ) *
          Real.log p * realPairIndicator side omega e := by
  rw [BPOrdered]
  apply Finset.sum_congr rfl
  intro p hp
  exact BpOrdered_selectedSet T side omega p

/-- Additive prime support can only shrink on passage to a selected subset. -/
theorem addPrimeSupport_selectedNat_subset
    {T : Finset ℕ} (S : Finset T) :
    addPrimeSupport (selectedNat S) ⊆ addPrimeSupport T := by
  intro p hp
  rw [addPrimeSupport] at hp ⊢
  obtain ⟨ab, hab, hp⟩ := Finset.mem_biUnion.mp hp
  have hab' := Finset.mem_filter.mp hab
  have hoff := Finset.mem_offDiag.mp hab'.1
  apply Finset.mem_biUnion.mpr
  exact ⟨ab, Finset.mem_filter.mpr
    ⟨Finset.mem_offDiag.mpr
      ⟨selectedNat_subset S hoff.1, selectedNat_subset S hoff.2.1,
        hoff.2.2⟩, hab'.2⟩, hp⟩

end

end Erdos126.SelectionBridge
