import Erdos126BiasGlobal

/-!
# A positive-density good event for the biased sample

The coupled iid Bernoulli-`1/4` subset supplies an exact second-moment bound
for the size of the biased selected set.  Everything is expressed using
uniform finite expectations and counting densities.
-/

open scoped BigOperators

namespace Erdos126.GoodEvent

open Erdos126.Bias Erdos126.BiasedSample Erdos126.BiasGlobal

variable {V : Type*} [Fintype V] [LinearOrder V]

instance : Nonempty (SystemSample V) :=
  ⟨⟨false, fun _ => 0⟩⟩

/-- Rational-valued size of the coupled iid Bernoulli-`1/4` subset. -/
def thinCount (side : V → Bool) (omega : SystemSample V) : ℚ :=
  ((thinSet side omega).card : ℕ)

/-- The good event asks the biased selected set to have at least `k/8`
vertices. -/
def Good (side : V → Bool) (k : ℕ) (omega : SystemSample V) : Prop :=
  (k : ℚ) / 8 ≤ ((selectedSet side omega).card : ℕ)

instance (side : V → Bool) (k : ℕ) : DecidablePred (Good side k) := by
  intro omega
  unfold Good
  infer_instance

omit [LinearOrder V] in
lemma thinCount_eq_sum (side : V → Bool) (omega : SystemSample V) :
    thinCount side omega =
      ∑ v : V, thinIndicator omega.orientation (side v) (omega.label v) := by
  simp [thinCount, thinSet, thinIndicator]

lemma thinIndicator_mul_self (orientation side : Bool) (label : Fin 4) :
    thinIndicator orientation side label * thinIndicator orientation side label =
      thinIndicator orientation side label := by
  by_cases h : thin orientation side label <;> simp [thinIndicator, h]

/-- In a nontrivial finite system, every thin vertex indicator has expectation
exactly `1/4`. -/
lemma expect_system_thin_vertex [Nontrivial V] (side : V → Bool) (v : V) :
    (𝔼 omega : SystemSample V,
      thinIndicator omega.orientation (side v) (omega.label v)) = 1 / 4 := by
  obtain ⟨w, hwv⟩ := exists_ne v
  change (𝔼 omega : SystemSample V,
    firstThinIndicator (side v)
      ⟨omega.orientation, omega.label v, omega.label w⟩) = 1 / 4
  calc
    _ = 𝔼 q : Sample, firstThinIndicator (side v) q :=
      expect_pairProjection v w hwv.symm _
    _ = 1 / 4 := expect_firstThinIndicator (side v)

lemma expect_thinCount [Nontrivial V] (side : V → Bool) :
    (𝔼 omega : SystemSample V, thinCount side omega) =
      (Fintype.card V : ℚ) / 4 := by
  simp_rw [thinCount_eq_sum, Finset.expect_sum_comm,
    expect_system_thin_vertex side]
  simp
  ring

lemma expect_thinCount_sq [Nontrivial V] (side : V → Bool) :
    (𝔼 omega : SystemSample V, (thinCount side omega) ^ 2) =
      (Fintype.card V : ℚ) ^ 2 / 16 + 3 * Fintype.card V / 16 := by
  simp_rw [thinCount_eq_sum, pow_two, Finset.sum_mul_sum]
  rw [Finset.expect_sum_comm]
  simp_rw [Finset.expect_sum_comm]
  have hproduct :
      (∑ x : V, ∑ y : V,
        𝔼 i : SystemSample V,
          thinIndicator i.orientation (side x) (i.label x) *
            thinIndicator i.orientation (side y) (i.label y)) =
      ∑ e ∈ (Finset.univ : Finset V) ×ˢ Finset.univ,
        𝔼 i : SystemSample V,
          thinIndicator i.orientation (side e.1) (i.label e.1) *
            thinIndicator i.orientation (side e.2) (i.label e.2) := by
    simpa using (Finset.sum_product (Finset.univ : Finset V) Finset.univ
      (fun e : V × V =>
        𝔼 i : SystemSample V,
          thinIndicator i.orientation (side e.1) (i.label e.1) *
            thinIndicator i.orientation (side e.2) (i.label e.2))).symm
  rw [hproduct]
  rw [← Finset.diag_union_offDiag (Finset.univ : Finset V)]
  rw [Finset.sum_union
    (Finset.disjoint_diag_offDiag (Finset.univ : Finset V))]
  have hdiag :
      (∑ e ∈ (Finset.univ : Finset V).diag,
        𝔼 omega : SystemSample V,
          thinIndicator omega.orientation (side e.1) (omega.label e.1) *
            thinIndicator omega.orientation (side e.2) (omega.label e.2)) =
        (Fintype.card V : ℚ) / 4 := by
    rw [Finset.sum_diag]
    simp_rw [thinIndicator_mul_self, expect_system_thin_vertex side]
    simp
    ring
  have hoff :
      (∑ e ∈ (Finset.univ : Finset V).offDiag,
        𝔼 omega : SystemSample V,
          thinIndicator omega.orientation (side e.1) (omega.label e.1) *
            thinIndicator omega.orientation (side e.2) (omega.label e.2)) =
        ((Finset.univ : Finset V).offDiag.card : ℚ) / 16 := by
    calc
      _ = ∑ _e ∈ (Finset.univ : Finset V).offDiag, (1 / 16 : ℚ) := by
        apply Finset.sum_congr rfl
        intro e he
        have hne : e.1 ≠ e.2 := (Finset.mem_offDiag.mp he).2.2
        exact expect_system_thin_pair side hne
      _ = ((Finset.univ : Finset V).offDiag.card : ℚ) / 16 := by
        simp
        ring
  rw [hdiag, hoff, Finset.offDiag_card, Finset.card_univ]
  have hk : 1 ≤ Fintype.card V := Fintype.card_pos
  have hle : Fintype.card V ≤ Fintype.card V * Fintype.card V := by
    nlinarith
  rw [Nat.cast_sub hle, Nat.cast_mul]
  ring

/-- Exact variance of the coupled iid count. -/
lemma expect_thinCount_sub_mean_sq [Nontrivial V] (side : V → Bool) :
    (𝔼 omega : SystemSample V,
      (thinCount side omega - (Fintype.card V : ℚ) / 4) ^ 2) =
      3 * (Fintype.card V : ℚ) / 16 := by
  have hpoint (omega : SystemSample V) :
      (thinCount side omega - (Fintype.card V : ℚ) / 4) ^ 2 =
        (thinCount side omega) ^ 2 -
          2 * ((Fintype.card V : ℚ) / 4) * thinCount side omega +
          ((Fintype.card V : ℚ) / 4) ^ 2 := by ring
  simp_rw [hpoint, Finset.expect_add_distrib, Finset.expect_sub_distrib]
  rw [expect_thinCount_sq]
  rw [← Finset.mul_expect (Finset.univ : Finset (SystemSample V))
    (thinCount side) (2 * ((Fintype.card V : ℚ) / 4))]
  rw [expect_thinCount]
  simp only [Fintype.expect_const]
  ring

/-- Density of outcomes whose biased selected set has size below `k/8`. -/
theorem bad_selected_density_le_twelve_div
    (side : V → Bool) (k : ℕ) (hk : 0 < k) (hcard : Fintype.card V = k) :
    (((Finset.univ.filter fun omega : SystemSample V =>
        ¬ Good side k omega).card : ℕ) : ℚ) /
        Fintype.card (SystemSample V) ≤ 12 / (k : ℚ) := by
  by_cases hk12 : k ≤ 12
  · have hden :
        (((Finset.univ.filter fun omega : SystemSample V =>
            ¬ Good side k omega).card : ℕ) : ℚ) /
            Fintype.card (SystemSample V) ≤ 1 := by
      rw [div_le_one]
      · exact_mod_cast Finset.card_le_univ _
      · positivity
    have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
    calc
      _ ≤ 1 := hden
      _ ≤ 12 / (k : ℚ) := (le_div_iff₀ hkq).mpr (by
        norm_num
        exact_mod_cast hk12)
  · have hklarge : 12 < k := Nat.lt_of_not_ge hk12
    have hcardlarge : 1 < Fintype.card V := by omega
    let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcardlarge
    have hthin := density_small_le_twelve_div k hk (thinCount side)
      (fun omega => by simp [thinCount]) (by
        rw [← hcard]
        exact (expect_thinCount_sub_mean_sq side).le)
    let badSelected : Finset (SystemSample V) :=
      Finset.univ.filter fun omega => ¬ Good side k omega
    let badThin : Finset (SystemSample V) :=
      Finset.univ.filter fun omega => thinCount side omega < (k : ℚ) / 8
    have hsubset : badSelected ⊆ badThin := by
      intro omega homega
      have hbad : ((selectedSet side omega).card : ℚ) < (k : ℚ) / 8 := by
        simpa [badSelected, Good] using (Finset.mem_filter.mp homega).2
      have hthinSub := thinSet_subset_selectedSet side omega
      have hcardle : (thinSet side omega).card ≤ (selectedSet side omega).card :=
        Finset.card_le_card hthinSub
      change omega ∈ badThin
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Nat.cast_le.mpr hcardle).trans_lt hbad⟩
    exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsubset))
      (by positivity)).trans (by simpa [badThin] using hthin)

/-- Restricting any quantity bounded above by `B` to a good event loses at
most `delta * B` in expectation.  No lower bound on the quantity is needed. -/
theorem expect_sub_badLoss_le_expect_restrict_good
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (F : Omega → ℚ) (GoodEvent : Omega → Prop) [DecidablePred GoodEvent]
    (B delta : ℚ) (hB : 0 ≤ B) (hFle : ∀ omega, F omega ≤ B)
    (hbad :
      (((Finset.univ.filter fun omega : Omega => ¬ GoodEvent omega).card : ℕ) : ℚ) /
        Fintype.card Omega ≤ delta) :
    (𝔼 omega, F omega) - delta * B ≤
      𝔼 omega, if GoodEvent omega then F omega else 0 := by
  let bad : Finset Omega := Finset.univ.filter fun omega => ¬ GoodEvent omega
  have hbadExpect :
      (𝔼 omega, if ¬ GoodEvent omega then F omega else 0) ≤ delta * B := by
    rw [Fintype.expect_eq_sum_div_card]
    calc
      (∑ omega : Omega, if ¬ GoodEvent omega then F omega else 0) /
          Fintype.card Omega = (∑ omega ∈ bad, F omega) / Fintype.card Omega := by
        congr 1
        rw [Finset.sum_filter]
      _ ≤ (bad.card * B) / Fintype.card Omega := by
        gcongr
        simpa using Finset.sum_le_card_nsmul bad F B fun omega _ => hFle omega
      _ = ((bad.card : ℚ) / Fintype.card Omega) * B := by ring
      _ ≤ delta * B := mul_le_mul_of_nonneg_right hbad hB
  have hsplit :
      (𝔼 omega, F omega) =
        (𝔼 omega, if GoodEvent omega then F omega else 0) +
          𝔼 omega, if ¬ GoodEvent omega then F omega else 0 := by
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro omega _
    by_cases h : GoodEvent omega <;> simp [h]
  rw [hsplit]
  linarith

omit [Fintype V] [LinearOrder V] in
lemma pairIndicator_nonneg (side : V → Bool) (omega : SystemSample V) (e : V × V) :
    0 ≤ pairIndicator side omega e := by
  unfold pairIndicator retainedIndicator
  split_ifs <;> norm_num

omit [Fintype V] [LinearOrder V] in
lemma pairIndicator_le_one (side : V → Bool) (omega : SystemSample V) (e : V × V) :
    pairIndicator side omega e ≤ 1 := by
  unfold pairIndicator retainedIndicator
  split_ifs <;> norm_num

/-- On the selected-size good event, a nonnegative off-diagonal edge mass
retains the advertised `(3/16 - 12/k)` fraction. -/
theorem good_restricted_edgeMass_ge
    (side : V → Bool) (k : ℕ) (hk : 0 < k) (hcard : Fintype.card V = k)
    (weight : V × V → ℚ) (hweight : ∀ e, 0 ≤ weight e) :
    (3 / 16 - 12 / (k : ℚ)) *
        (∑ e ∈ (Finset.univ : Finset V).offDiag, weight e) ≤
      𝔼 omega : SystemSample V,
        if Good side k omega then
          ∑ e ∈ (Finset.univ : Finset V).offDiag,
            weight e * pairIndicator side omega e
        else 0 := by
  let B : ℚ := ∑ e ∈ (Finset.univ : Finset V).offDiag, weight e
  let F : SystemSample V → ℚ := fun omega =>
    ∑ e ∈ (Finset.univ : Finset V).offDiag,
      weight e * pairIndicator side omega e
  apply expect_restrict_good_ge F (Good side k) B (3 / 16) (12 / (k : ℚ))
  · exact Finset.sum_nonneg fun e _ => hweight e
  · intro omega
    exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (hweight e) (pairIndicator_nonneg side omega e)
  · intro omega
    change (∑ e ∈ (Finset.univ : Finset V).offDiag,
      weight e * pairIndicator side omega e) ≤
        ∑ e ∈ (Finset.univ : Finset V).offDiag, weight e
    apply Finset.sum_le_sum
    intro e _
    simpa using mul_le_mul_of_nonneg_left
      (pairIndicator_le_one side omega e) (hweight e)
  · simpa [F] using
      three_sixteenths_weight_le_expect_retained_offDiag side weight hweight
  · exact bad_selected_density_le_twelve_div side k hk hcard

/-- Component-slack restriction in its abstract reusable form: any total
slack bounded above by `B` loses at most `(12/k)B` on the good event. -/
theorem componentSlack_badLoss_le_good
    (side : V → Bool) (k : ℕ) (hk : 0 < k) (hcard : Fintype.card V = k)
    (slack : SystemSample V → ℚ) (B : ℚ) (hB : 0 ≤ B)
    (hslack_le : ∀ omega, slack omega ≤ B) :
    (𝔼 omega, slack omega) - (12 / (k : ℚ)) * B ≤
      𝔼 omega, if Good side k omega then slack omega else 0 := by
  exact expect_sub_badLoss_le_expect_restrict_good slack (Good side k) B
    (12 / (k : ℚ)) hB hslack_le
    (bad_selected_density_le_twelve_div side k hk hcard)

end Erdos126.GoodEvent
