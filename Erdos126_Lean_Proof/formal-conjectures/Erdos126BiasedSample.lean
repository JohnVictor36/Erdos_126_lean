import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The finite biased sample used for Erdős problem 126

This file gives a completely finite model of the local biased-selection
experiment.  An orientation bit decides which of a paired pair of classes is
favoured.  Independently, each of two vertices receives a uniform label in
`Fin 4`; a vertex in the favoured class keeps three labels and a vertex in the
other class keeps one.  The two label coordinates represent any two distinct
vertices, so the pair computations below are the local marginals of the full
product experiment.

We also single out one of the three retained labels on the favoured side.  On
the other side the unique retained label is used.  This couples an iid
Bernoulli-`1/4` selection pointwise below the biased selection.
-/

open scoped BigOperators

namespace Erdos126.BiasedSample

/-- The exact finite sample for an ordered pair of distinct vertices. -/
@[ext]
structure Sample where
  orientation : Bool
  firstLabel : Fin 4
  secondLabel : Fin 4
  deriving DecidableEq, Fintype

/-- Coordinates identify the 32-point sample with an explicit product.  This
equivalence lets the exact probability calculations below be checked by the
kernel after expanding three genuinely finite sums. -/
def sampleEquiv : Sample ≃ Bool × Fin 4 × Fin 4 where
  toFun s := (s.orientation, s.firstLabel, s.secondLabel)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rewrite expectation on `Sample` as expectation on its three explicit
coordinates. -/
lemma expect_eq_explicit (F : Sample → ℚ) :
    (𝔼 s : Sample, F s) =
      𝔼 q : Bool × Fin 4 × Fin 4, F ⟨q.1, q.2.1, q.2.2⟩ := by
  exact Fintype.expect_equiv sampleEquiv F
    (fun q => F ⟨q.1, q.2.1, q.2.2⟩) (fun _ => rfl)

/-- A vertex is retained with probability `3/4` when its class agrees with the
orientation and with probability `1/4` otherwise. -/
def retained (orientation side : Bool) (label : Fin 4) : Prop :=
  if orientation = side then label ≠ 0 else label = 0

instance (orientation side : Bool) (label : Fin 4) :
    Decidable (retained orientation side label) := by
  unfold retained
  infer_instance

/-- Indicator of membership in the biased selection. -/
def retainedIndicator (orientation side : Bool) (label : Fin 4) : ℚ :=
  if retained orientation side label then 1 else 0

/-- The first vertex indicator in the two-coordinate sample. -/
def firstIndicator (side : Bool) (omega : Sample) : ℚ :=
  retainedIndicator omega.orientation side omega.firstLabel

/-- The second vertex indicator in the two-coordinate sample. -/
def secondIndicator (side : Bool) (omega : Sample) : ℚ :=
  retainedIndicator omega.orientation side omega.secondLabel

/-- The coupled Bernoulli-`1/4` event.  On the favoured side it uses label `1`;
on the other side it uses the unique retained label `0`. -/
def thin (orientation side : Bool) (label : Fin 4) : Prop :=
  label = if orientation = side then 1 else 0

instance (orientation side : Bool) (label : Fin 4) :
    Decidable (thin orientation side label) := by
  unfold thin
  infer_instance

/-- Indicator of membership in the coupled iid Bernoulli-`1/4` subset. -/
def thinIndicator (orientation side : Bool) (label : Fin 4) : ℚ :=
  if thin orientation side label then 1 else 0

def firstThinIndicator (side : Bool) (omega : Sample) : ℚ :=
  thinIndicator omega.orientation side omega.firstLabel

def secondThinIndicator (side : Bool) (omega : Sample) : ℚ :=
  thinIndicator omega.orientation side omega.secondLabel

/-- The biased selection has marginal retention probability `1/2`. -/
theorem expect_firstIndicator (side : Bool) :
    (𝔼 omega : Sample, firstIndicator side omega) = 1 / 2 := by
  cases side <;> rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card,
    Fintype.sum_prod_type] <;> simp_rw [Fintype.sum_prod_type] <;>
    rw [Fintype.sum_bool] <;> simp_rw [Fin.sum_univ_four] <;>
    norm_num [firstIndicator, retainedIndicator, retained, Fin.ext_iff]

/-- The second coordinate has the same marginal. -/
theorem expect_secondIndicator (side : Bool) :
    (𝔼 omega : Sample, secondIndicator side omega) = 1 / 2 := by
  cases side <;> rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card,
    Fintype.sum_prod_type] <;> simp_rw [Fintype.sum_prod_type] <;>
    rw [Fintype.sum_bool] <;> simp_rw [Fin.sum_univ_four] <;>
    norm_num [secondIndicator, retainedIndicator, retained, Fin.ext_iff]

/-- Two distinct vertices in the same class survive together with probability
`(9/16 + 1/16)/2 = 5/16`. -/
theorem expect_sameSide_pair (side : Bool) :
    (𝔼 omega : Sample,
      firstIndicator side omega * secondIndicator side omega) = 5 / 16 := by
  cases side <;> rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card,
    Fintype.sum_prod_type] <;> simp_rw [Fintype.sum_prod_type] <;>
    rw [Fintype.sum_bool] <;> simp_rw [Fin.sum_univ_four] <;>
    norm_num [firstIndicator, secondIndicator, retainedIndicator, retained, Fin.ext_iff]

/-- Two distinct vertices in opposite classes survive together with
probability `3/16`, independently of the orientation. -/
theorem expect_oppositeSide_pair (side : Bool) :
    (𝔼 omega : Sample,
      firstIndicator side omega * secondIndicator (!side) omega) = 3 / 16 := by
  cases side <;> rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card,
    Fintype.sum_prod_type] <;> simp_rw [Fintype.sum_prod_type] <;>
    rw [Fintype.sum_bool] <;> simp_rw [Fin.sum_univ_four] <;>
    norm_num [firstIndicator, secondIndicator, retainedIndicator, retained, Fin.ext_iff]

/-- The coupled thin event is pointwise contained in the biased event. -/
theorem thin_imp_retained (orientation side : Bool) (label : Fin 4) :
    thin orientation side label → retained orientation side label := by
  cases orientation <;> cases side <;> fin_cases label <;> simp [thin, retained]

theorem thinIndicator_le_retainedIndicator
    (orientation side : Bool) (label : Fin 4) :
    thinIndicator orientation side label ≤ retainedIndicator orientation side label := by
  by_cases h : thin orientation side label
  · simp [thinIndicator, retainedIndicator, h, thin_imp_retained _ _ _ h]
  · by_cases hr : retained orientation side label <;>
      simp [thinIndicator, retainedIndicator, h, hr]

/-- Each vertex belongs to the coupled thin subset with probability `1/4`. -/
theorem expect_firstThinIndicator (side : Bool) :
    (𝔼 omega : Sample, firstThinIndicator side omega) = 1 / 4 := by
  cases side <;> rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card,
    Fintype.sum_prod_type] <;> simp_rw [Fintype.sum_prod_type] <;>
    rw [Fintype.sum_bool] <;> simp_rw [Fin.sum_univ_four] <;>
    norm_num [firstThinIndicator, thinIndicator, thin, Fin.ext_iff]

/-- The two thin coordinates are independent Bernoulli-`1/4`: their joint
probability is `1/16`, for arbitrary choices of their two class sides. -/
theorem expect_thin_pair (firstSide secondSide : Bool) :
    (𝔼 omega : Sample,
      firstThinIndicator firstSide omega * secondThinIndicator secondSide omega) = 1 / 16 := by
  cases firstSide <;> cases secondSide <;>
    rw [expect_eq_explicit, Fintype.expect_eq_sum_div_card, Fintype.sum_prod_type] <;>
    simp_rw [Fintype.sum_prod_type] <;> rw [Fintype.sum_bool] <;>
    simp_rw [Fin.sum_univ_four] <;>
    norm_num [firstThinIndicator, secondThinIndicator, thinIndicator, thin, Fin.ext_iff]

/-- Coupling below the biased selection, stated directly for both coordinates. -/
theorem thin_pair_pointwise_below (firstSide secondSide : Bool) (omega : Sample) :
    firstThinIndicator firstSide omega ≤ firstIndicator firstSide omega ∧
      secondThinIndicator secondSide omega ≤ secondIndicator secondSide omega := by
  exact ⟨thinIndicator_le_retainedIndicator _ _ _,
    thinIndicator_le_retainedIndicator _ _ _⟩

section FullSystem

/-- The full finite product sample on an arbitrary finite vertex system. -/
@[ext]
structure SystemSample (V : Type*) where
  orientation : Bool
  label : V → Fin 4

instance (V : Type*) [Fintype V] [DecidableEq V] : Fintype (SystemSample V) :=
  Fintype.ofEquiv (Bool × (V → Fin 4))
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun omega => (omega.orientation, omega.label)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The biased selected subset in the full product sample. -/
def selectedSet (side : V → Bool) (omega : SystemSample V) : Finset V :=
  Finset.univ.filter fun v => retained omega.orientation (side v) (omega.label v)

/-- The coupled iid Bernoulli-`1/4` subset. -/
def thinSet (side : V → Bool) (omega : SystemSample V) : Finset V :=
  Finset.univ.filter fun v => thin omega.orientation (side v) (omega.label v)

omit [DecidableEq V] in
/-- The iid Bernoulli-`1/4` subset is pointwise below the biased subset. -/
theorem thinSet_subset_selectedSet (side : V → Bool) (omega : SystemSample V) :
    thinSet side omega ⊆ selectedSet side omega := by
  intro v hv
  simp only [thinSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact thin_imp_retained _ _ _ hv

/-- Splitting off two distinct label coordinates identifies their marginal
with `Sample`; all remaining independent labels form the second factor. -/
def pairSplitEquiv (u v : V) (huv : u ≠ v) :
    SystemSample V ≃
      Sample × ({x : V // x ≠ u ∧ x ≠ v} → Fin 4) where
  toFun omega :=
    (⟨omega.orientation, omega.label u, omega.label v⟩, fun x => omega.label x)
  invFun q :=
    ⟨q.1.orientation, fun x =>
      if hxu : x = u then q.1.firstLabel
      else if hxv : x = v then q.1.secondLabel
      else q.2 ⟨x, hxu, hxv⟩⟩
  left_inv omega := by
    ext x
    · rfl
    · by_cases hxu : x = u
      · subst x
        simp
      · by_cases hxv : x = v
        · subst x
          simp [hxu]
        · simp [hxu, hxv]
  right_inv q := by
    rcases q with ⟨⟨orientation, firstLabel, secondLabel⟩, rest⟩
    apply Prod.ext
    · apply Sample.ext
      · rfl
      · simp
      · simp [huv.symm]
    · funext x
      simp [x.property.1, x.property.2]

/-- Expectation of a function of two distinct vertices agrees with expectation
in the explicit 32-point pair sample. -/
theorem expect_pairProjection (u v : V) (huv : u ≠ v) (F : Sample → ℚ) :
    (𝔼 omega : SystemSample V,
      F ⟨omega.orientation, omega.label u, omega.label v⟩) =
      𝔼 omega : Sample, F omega := by
  rw [Fintype.expect_equiv (pairSplitEquiv u v huv)
    (fun omega : SystemSample V =>
      F ⟨omega.orientation, omega.label u, omega.label v⟩)
    (fun q : Sample × ({x : V // x ≠ u ∧ x ≠ v} → Fin 4) => F q.1) (by
      intro omega
      rfl)]
  rw [show (𝔼 q : Sample × ({x : V // x ≠ u ∧ x ≠ v} → Fin 4), F q.1) =
      𝔼 s : Sample, 𝔼 _r : ({x : V // x ≠ u ∧ x ≠ v} → Fin 4), F s by
    simpa using Finset.expect_product (Finset.univ : Finset Sample)
      (Finset.univ : Finset ({x : V // x ≠ u ∧ x ≠ v} → Fin 4))
      (fun q => F q.1)]
  simp

/-- Global-system same-class pair probability. -/
theorem expect_system_sameSide_pair (side : V → Bool) {u v : V} (huv : u ≠ v)
    (hsame : side u = side v) :
    (𝔼 omega : SystemSample V,
      retainedIndicator omega.orientation (side u) (omega.label u) *
        retainedIndicator omega.orientation (side v) (omega.label v)) = 5 / 16 := by
  change (𝔼 omega : SystemSample V,
    (fun q : Sample => firstIndicator (side u) q * secondIndicator (side v) q)
      ⟨omega.orientation, omega.label u, omega.label v⟩) = 5 / 16
  calc
    _ = 𝔼 q : Sample, firstIndicator (side u) q * secondIndicator (side v) q :=
      expect_pairProjection u v huv _
    _ = 5 / 16 := by rw [hsame]; exact expect_sameSide_pair (side v)

/-- Global-system opposite-class pair probability. -/
theorem expect_system_oppositeSide_pair (side : V → Bool) {u v : V} (huv : u ≠ v)
    (hopp : side v = !(side u)) :
    (𝔼 omega : SystemSample V,
      retainedIndicator omega.orientation (side u) (omega.label u) *
        retainedIndicator omega.orientation (side v) (omega.label v)) = 3 / 16 := by
  change (𝔼 omega : SystemSample V,
    (fun q : Sample => firstIndicator (side u) q * secondIndicator (side v) q)
      ⟨omega.orientation, omega.label u, omega.label v⟩) = 3 / 16
  calc
    _ = 𝔼 q : Sample, firstIndicator (side u) q * secondIndicator (side v) q :=
      expect_pairProjection u v huv _
    _ = 3 / 16 := by rw [hopp]; exact expect_oppositeSide_pair (side u)

/-- Any two distinct vertices in the coupled subset have joint probability
`1/16`, the pairwise iid Bernoulli-`1/4` identity. -/
theorem expect_system_thin_pair (side : V → Bool) {u v : V} (huv : u ≠ v) :
    (𝔼 omega : SystemSample V,
      thinIndicator omega.orientation (side u) (omega.label u) *
        thinIndicator omega.orientation (side v) (omega.label v)) = 1 / 16 := by
  change (𝔼 omega : SystemSample V,
    (fun q : Sample => firstThinIndicator (side u) q * secondThinIndicator (side v) q)
      ⟨omega.orientation, omega.label u, omega.label v⟩) = 1 / 16
  calc
    _ = 𝔼 q : Sample,
        firstThinIndicator (side u) q * secondThinIndicator (side v) q :=
      expect_pairProjection u v huv _
    _ = 1 / 16 := expect_thin_pair (side u) (side v)

end FullSystem

end Erdos126.BiasedSample
