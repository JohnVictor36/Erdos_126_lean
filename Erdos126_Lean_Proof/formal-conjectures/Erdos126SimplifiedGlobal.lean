import Erdos126AmbientIdentity
import Erdos126MetricSum
import Erdos126DeterministicSplit
import Erdos126ZeroRemoval

/-!
# Deterministic global integration

For each support prime `p`, split the set by its canonical `p`-unit side,
optimize the p-adic involutions on the two sides, and paste them into one
ambient involution.  A single metric estimate bounds the pasted cost; neither
side needs to be large.
-/

namespace Erdos126

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 1000000

/-- A positive set with two distinct elements has nonempty additive prime
support. -/
theorem addPrimeSupport_nonempty_of_two_le_deterministic
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    (addPrimeSupport T).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  have habSumPos : 0 < a + b := Nat.add_pos_left (hT a ha) b
  have habSumNeOne : a + b ≠ 1 := by
    have hap := hT a ha
    have hbp := hT b hb
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd habSumNeOne
  have hpSum : p ∈ (a + b).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, habSumPos.ne'⟩
  exact ⟨p, primeFactors_sum_subset_addPrimeSupport ha hb hab hpSum⟩

/-- The ordered normalized-sum potential is positive once an off-diagonal
edge exists. -/
theorem AweightOrdered_pos_deterministic
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    0 < AweightOrdered T := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  rw [AweightOrdered]
  apply Finset.sum_pos'
  · intro e he
    have he' := Finset.mem_offDiag.mp he
    apply Real.log_nonneg
    have htwo := Normalized.two_le_normalizedSum
      (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2
    exact_mod_cast (show 1 ≤ Normalized.normalizedSum e.1 e.2 by omega)
  · refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, ?_⟩
    apply Real.log_pos
    have htwo := Normalized.two_le_normalizedSum
      (hT a ha) (hT b hb) hab
    exact_mod_cast htwo

/-- The logarithmic ambient gap is nonnegative for every positive set and
every finite set of primes. -/
theorem ambientGap_nonneg_over
    (S P : Finset ℕ) (hS : ∀ a ∈ S, 0 < a)
    (hprime : ∀ q ∈ P, q.Prime) :
    0 ≤ AweightOrdered S - BPOrdered P S := by
  apply sub_nonneg.mpr
  have hPB := BPOrdered_le_BweightOrdered S hS P hprime
  have hBA : BweightOrdered S ≤ AweightOrdered S := by
    unfold BweightOrdered AweightOrdered
    apply Finset.sum_le_sum
    intro e he
    have he' := Finset.mem_offDiag.mp he
    have hD : 0 < (Normalized.normalizedDist e.1 e.2 : ℝ) := by
      exact_mod_cast Normalized.normalizedDist_pos
        (hS e.1 he'.1) (hS e.2 he'.2.1) he'.2.2
    apply Real.log_le_log hD
    exact_mod_cast (normalizedDist_lt_normalizedSum
      (hS e.1 he'.1) (hS e.2 he'.2.1) he'.2.2).le
  exact hPB.trans hBA

/-- On one canonical side of `p`, the full `p`-difference mass is bounded by
the total endpoint cost of simultaneous p-adic involutions for the ambient
prime set. -/
theorem exists_pSide_involutions_cost_ge_Bp
    (T P : Finset ℕ) (p : ℕ) (side : Bool)
    (hT : ∀ a ∈ T, 0 < a) (hprime : ∀ q ∈ P, q.Prime)
    (hsupportT : addPrimeSupport T ⊆ P) (hpP : p ∈ P) :
    ∃ τ : ℕ → pSide T p side → pSide T p side,
      (∀ q ∈ P, Function.Involutive (τ q)) ∧
      BpOrdered p (pSide T p side) ≤
        ∑ q ∈ P, Real.log q * (involutionCost q (τ q) : ℝ) := by
  classical
  let S := pSide T p side
  have hSsub : S ⊆ T := pSide_subset T p side
  have hS : ∀ a ∈ S, 0 < a := by
    intro a ha
    exact hT a (hSsub ha)
  have hsupport : addPrimeSupport S ⊆ P := by
    exact (addPrimeSupport_mono hSsub).trans hsupportT
  obtain ⟨τ, hτinv, hτslack, hidentity⟩ :=
    exists_involutions_logged_identity_over S P hS hprime hsupport
  refine ⟨τ, hτinv, ?_⟩
  have hp := hprime p hpP
  have hgap : 0 ≤ AweightOrdered S - BPOrdered P S :=
    ambientGap_nonneg_over S P hS hprime
  have hlog (q : ℕ) (hq : q ∈ P) : 0 ≤ Real.log q := by
    exact Real.log_nonneg (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hprime q hq).ne_zero))
  have hrest :
      0 ≤ ∑ q ∈ P.erase p,
        Real.log q * pSlack q S (τ q) := by
    apply Finset.sum_nonneg
    intro q hq
    have hqP := (Finset.mem_erase.mp hq).2
    exact mul_nonneg (hlog q hqP) (hτslack q hqP)
  have hsplit :
      (∑ q ∈ P, Real.log q * pSlack q S (τ q)) =
        Real.log p * pSlack p S (τ p) +
          ∑ q ∈ P.erase p, Real.log q * pSlack q S (τ q) := by
    rw [← Finset.add_sum_erase _ _ hpP]
  have hheavy :
      BpOrdered p S ≤
        ∑ q ∈ P, Real.log q * pSlack q S (τ q) := by
    have hpExact : Real.log p * pSlack p S (τ p) = BpOrdered p S := by
      simpa only [S] using
        (log_mul_pSlack_pSide_eq_BpOrdered T p side hp hT (τ p))
    rw [hsplit, ← hpExact]
    exact le_add_of_nonneg_right hrest
  calc
    BpOrdered p S ≤
        ∑ q ∈ P, Real.log q * pSlack q S (τ q) := hheavy
    _ ≤ (AweightOrdered S - BPOrdered P S) +
          ∑ q ∈ P, Real.log q * pSlack q S (τ q) :=
      le_add_of_nonneg_left hgap
    _ = ∑ q ∈ P, Real.log q * (involutionCost q (τ q) : ℝ) :=
      hidentity

/-- Pasting the two side systems produces ambient involutions whose total
endpoint cost dominates the complete `p`-difference mass. -/
theorem exists_ambient_involutions_cost_ge_Bp
    (T P : Finset ℕ) (p : ℕ)
    (hT : ∀ a ∈ T, 0 < a) (hprime : ∀ q ∈ P, q.Prime)
    (hsupportT : addPrimeSupport T ⊆ P) (hpP : p ∈ P) :
    ∃ τ : ℕ → T → T,
      (∀ q ∈ P, Function.Involutive (τ q)) ∧
      BpOrdered p T ≤
        ∑ q ∈ P, Real.log q * (involutionCost q (τ q) : ℝ) := by
  classical
  obtain ⟨τ0, hτ0inv, hτ0cost⟩ :=
    exists_pSide_involutions_cost_ge_Bp
      T P p false hT hprime hsupportT hpP
  obtain ⟨τ1, hτ1inv, hτ1cost⟩ :=
    exists_pSide_involutions_cost_ge_Bp
      T P p true hT hprime hsupportT hpP
  let τ : ℕ → T → T := fun q => gluePSideMaps T p (τ0 q) (τ1 q)
  refine ⟨τ, ?_, ?_⟩
  · intro q hq
    exact gluePSideMaps_involutive T p (τ0 q) (τ1 q)
      (hτ0inv q hq) (hτ1inv q hq)
  · rw [BpOrdered_pSide_partition T p (hprime p hpP) hT]
    calc
      BpOrdered p (pSide T p false) + BpOrdered p (pSide T p true) ≤
          (∑ q ∈ P, Real.log q * (involutionCost q (τ0 q) : ℝ)) +
            ∑ q ∈ P, Real.log q * (involutionCost q (τ1 q) : ℝ) :=
        add_le_add hτ0cost hτ1cost
      _ = ∑ q ∈ P,
          Real.log q *
            ((involutionCost q (τ0 q) : ℝ) + involutionCost q (τ1 q)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = ∑ q ∈ P, Real.log q * (involutionCost q (τ q) : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [τ]
        rw [involutionCost_gluePSideMaps]
        push_cast
        rfl

/-- One prime's complete normalized difference mass is bounded on the
ambient scale.  Notice that the metric lemma is used only once, after the two
side involutions have been pasted together. -/
theorem card_mul_BpOrdered_le_six_support_mul_AweightOrdered
    (T P : Finset ℕ) (p : ℕ)
    (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (hprime : ∀ q ∈ P, q.Prime)
    (hsupportT : addPrimeSupport T ⊆ P) (hpP : p ∈ P) :
    (T.card : ℝ) * BpOrdered p T ≤
      6 * (P.card : ℝ) * AweightOrdered T := by
  obtain ⟨τ, hτinv, hτcost⟩ :=
    exists_ambient_involutions_cost_ge_Bp
      T P p hT hprime hsupportT hpP
  have hmul := mul_le_mul_of_nonneg_left hτcost
    (by positivity : 0 ≤ (T.card : ℝ))
  exact hmul.trans
    (card_mul_sum_log_involutionCost_le_six_card_mul_AweightOrdered
      T hT hcard P hprime τ hτinv)

/-- Sum the one-prime deterministic estimate over the ambient support. -/
theorem card_mul_BPOrdered_le_six_support_sq_mul_AweightOrdered
    (T P : Finset ℕ)
    (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (hprime : ∀ q ∈ P, q.Prime)
    (hsupportT : addPrimeSupport T ⊆ P) :
    (T.card : ℝ) * BPOrdered P T ≤
      6 * (P.card : ℝ) ^ 2 * AweightOrdered T := by
  rw [BPOrdered, Finset.mul_sum]
  calc
    (∑ p ∈ P, (T.card : ℝ) * BpOrdered p T) ≤
        ∑ p ∈ P, 6 * (P.card : ℝ) * AweightOrdered T := by
      exact Finset.sum_le_sum fun p hp ↦
        card_mul_BpOrdered_le_six_support_mul_AweightOrdered
          T P p hT hcard hprime hsupportT hp
    _ = 6 * (P.card : ℝ) ^ 2 * AweightOrdered T := by
      simp
      ring

/-- The ambient archimedean gap is controlled by one ordinary simultaneous
matching system. -/
theorem card_mul_ambientGap_le_six_support_mul_AweightOrdered
    (T P : Finset ℕ)
    (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card)
    (hprime : ∀ q ∈ P, q.Prime)
    (hsupportT : addPrimeSupport T ⊆ P) :
    (T.card : ℝ) * (AweightOrdered T - BPOrdered P T) ≤
      6 * (P.card : ℝ) * AweightOrdered T := by
  obtain ⟨τ, hτinv, hτslack, hidentity⟩ :=
    exists_involutions_logged_identity_over T P hT hprime hsupportT
  have hlog (q : ℕ) (hq : q ∈ P) : 0 ≤ Real.log q := by
    exact Real.log_nonneg (by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hprime q hq).ne_zero))
  have hslackSum :
      0 ≤ ∑ q ∈ P, Real.log q * pSlack q T (τ q) := by
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (hlog q hq) (hτslack q hq)
  have hgapCost :
      AweightOrdered T - BPOrdered P T ≤
        ∑ q ∈ P, Real.log q * (involutionCost q (τ q) : ℝ) := by
    calc
      AweightOrdered T - BPOrdered P T ≤
          (AweightOrdered T - BPOrdered P T) +
            ∑ q ∈ P, Real.log q * pSlack q T (τ q) :=
        le_add_of_nonneg_right hslackSum
      _ = ∑ q ∈ P,
          Real.log q * (involutionCost q (τ q) : ℝ) := hidentity
  have hmul := mul_le_mul_of_nonneg_left hgapCost
    (by positivity : 0 ≤ (T.card : ℝ))
  exact hmul.trans
    (card_mul_sum_log_involutionCost_le_six_card_mul_AweightOrdered
      T hT hcard P hprime τ hτinv)

/-- Deterministic positive-set bound.  The proof contains no sampling and has
the exact coefficient `6 r (r+1)`, weakened here to `12 r²`. -/
theorem positive_card_le_12_support_sq_deterministic
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    T.card ≤ 12 * (addPrimeSupport T).card ^ 2 := by
  classical
  let P := addPrimeSupport T
  have hPnonempty : P.Nonempty :=
    addPrimeSupport_nonempty_of_two_le_deterministic T hT hcard
  have hrNat : 0 < P.card := Finset.card_pos.mpr hPnonempty
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact prime_of_mem_addPrimeSupport hq
  have hsupport : addPrimeSupport T ⊆ P := by
    exact Finset.Subset.rfl
  have hA : 0 < AweightOrdered T :=
    AweightOrdered_pos_deterministic T hT hcard
  have hgap := card_mul_ambientGap_le_six_support_mul_AweightOrdered
    T P hT hcard hprime hsupport
  have hBP := card_mul_BPOrdered_le_six_support_sq_mul_AweightOrdered
    T P hT hcard hprime hsupport
  have hcombined :
      (T.card : ℝ) * AweightOrdered T ≤
        6 * (P.card : ℝ) * ((P.card : ℝ) + 1) *
          AweightOrdered T := by
    calc
      (T.card : ℝ) * AweightOrdered T =
          (T.card : ℝ) * (AweightOrdered T - BPOrdered P T) +
            (T.card : ℝ) * BPOrdered P T := by ring
      _ ≤ 6 * (P.card : ℝ) * AweightOrdered T +
          6 * (P.card : ℝ) ^ 2 * AweightOrdered T :=
        add_le_add hgap hBP
      _ = 6 * (P.card : ℝ) * ((P.card : ℝ) + 1) *
          AweightOrdered T := by ring
  have hreal : (T.card : ℝ) ≤
      6 * (P.card : ℝ) * ((P.card : ℝ) + 1) := by
    have hcombined' :
        AweightOrdered T * (T.card : ℝ) ≤
          AweightOrdered T *
            (6 * (P.card : ℝ) * ((P.card : ℝ) + 1)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hcombined
    exact (mul_le_mul_iff_right₀ hA).mp hcombined'
  have hreal12 : (T.card : ℝ) ≤ 12 * (P.card : ℝ) ^ 2 := by
    have hrOneNat : 1 ≤ P.card :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hrNat)
    have hr1 : (1 : ℝ) ≤ P.card := by exact_mod_cast hrOneNat
    nlinarith
  have hNat : T.card ≤ 12 * P.card ^ 2 := by
    exact_mod_cast hreal12
  simpa only [P] using hNat

/-- Arbitrary natural-number finsets: erase a possible zero and absorb the
single lost vertex. -/
theorem finite_quadratic_prime_support_bound_deterministic
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 13 * (addPrimeSupport A).card ^ 2 := by
  simpa using card_le_succ_mul_support_sq_of_positive_bound
    12 positive_card_le_12_support_sq_deterministic A hcard

end

end Erdos126
