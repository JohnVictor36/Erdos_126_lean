import Erdos126Global
import Erdos126AmbientIdentity
import Erdos126PotentialSelection
import Erdos126HeavyGood
import Erdos126MetricSum
import Erdos126ZeroRemoval

/-!
# End-to-end global integration
-/

namespace Erdos126

open scoped BigOperators
open BiasedSample BiasGlobal GoodEvent
open RealGoodEvent SelectionBridge HeavyPrimeBias HeavySelectionBridge

noncomputable section

set_option maxHeartbeats 1000000

/-- The concrete probabilistic and metric construction supplies the exact
expectation sandwich isolated in `Erdos126Global`. -/
theorem globalExpectationGlue : GlobalExpectationGlue := by
  intro T hT hkLarge
  classical
  let P := addPrimeSupport T
  have hk : 0 < T.card := by omega
  have hcard2 : 2 ≤ T.card := by omega
  have hPnonempty : P.Nonempty := by
    exact addPrimeSupport_nonempty_of_two_le T hT hcard2
  have hrNat : 0 < P.card := Finset.card_pos.mpr hPnonempty
  have hr : (0 : ℝ) < P.card := by exact_mod_cast hrNat
  have hprime : ∀ q ∈ P, q.Prime := by
    intro q hq
    exact prime_of_mem_addPrimeSupport hq
  obtain ⟨p, hpP, hpHeavy⟩ := exists_BpOrdered_ge_average P T hPnonempty
  have hp : p.Prime := hprime p hpP
  obtain ⟨tauHeavy, htauHeavy, hHeavyGood⟩ :=
    exists_good_heavy_slack T p hp hT hk
  let side : T → Bool := fun a => Padic.pUnitSide p a
  let S : SystemSample T → Finset ℕ := fun omega =>
    selectedNat (selectedSet side omega)
  have hSsub (omega : SystemSample T) : S omega ⊆ T := by
    exact selectedNat_subset _
  have hSpos (omega : SystemSample T) : ∀ a ∈ S omega, 0 < a := by
    exact selectedNat_pos _ hT
  have hSsupport (omega : SystemSample T) : addPrimeSupport (S omega) ⊆ P := by
    exact addPrimeSupport_selectedNat_subset _
  have hHeavyCert (omega : SystemSample T) :
      ∃ sigma : S omega → S omega,
        Function.Involutive sigma ∧
        (selectedPadicSlack T p tauHeavy omega : ℝ) ≤
          pSlack p (S omega) sigma ∧
        0 ≤ pSlack p (S omega) sigma := by
    obtain ⟨sigma, hsigma, hdom, hnonneg, hupper⟩ :=
      exists_selected_optimal_dominates_selectedPadicSlack
        T p hp hT tauHeavy htauHeavy omega
    exact ⟨sigma, hsigma, hdom, hnonneg⟩
  have hGeneralCert (omega : SystemSample T) (q : ℕ) (hq : q.Prime) :
      ∃ sigma : S omega → S omega,
        Function.Involutive sigma ∧ 0 ≤ pSlack q (S omega) sigma := by
    obtain ⟨sigma, hsigma, hweighted⟩ :=
      Padic.exists_involution_weighted (S omega) q hq (hSpos omega)
    refine ⟨sigma, hsigma, ?_⟩
    simp only [pSlack]
    exact sub_nonneg.mpr (by exact_mod_cast hweighted)
  let sigma : (omega : SystemSample T) → ℕ → S omega → S omega :=
    fun omega q =>
      if hqp : q = p then Classical.choose (hHeavyCert omega)
      else if hq : q.Prime then Classical.choose (hGeneralCert omega q hq)
      else id
  have hsigmaInv (omega : SystemSample T) (q : ℕ) (hqP : q ∈ P) :
      Function.Involutive (sigma omega q) := by
    have hq := hprime q hqP
    dsimp only [sigma]
    split_ifs with hqp _hq'
    · exact (Classical.choose_spec (hHeavyCert omega)).1
    · exact (Classical.choose_spec (hGeneralCert omega q hq)).1
  have hsigmaNonneg (omega : SystemSample T) (q : ℕ) (hqP : q ∈ P) :
      0 ≤ pSlack q (S omega) (sigma omega q) := by
    have hq := hprime q hqP
    dsimp only [sigma]
    split_ifs with hqp _hq'
    · subst q
      exact (Classical.choose_spec (hHeavyCert omega)).2.2
    · exact (Classical.choose_spec (hGeneralCert omega q hq)).2
  have hsigmaHeavy (omega : SystemSample T) :
      (selectedPadicSlack T p tauHeavy omega : ℝ) ≤
        pSlack p (S omega) (sigma omega p) := by
    dsimp only [sigma]
    rw [dif_pos rfl]
    exact (Classical.choose_spec (hHeavyCert omega)).2.1
  let L : SystemSample T → ℝ := fun omega =>
    AweightOrdered (S omega) - BPOrdered P (S omega) +
      ∑ q ∈ P, Real.log q * pSlack q (S omega) (sigma omega q)
  have hidentity (omega : SystemSample T) :
      L omega =
        ∑ q ∈ P,
          Real.log q * (involutionCost q (sigma omega q) : ℝ) := by
    exact logged_involution_identity_over
      (S omega) P (hSpos omega) hprime (hSsupport omega) (sigma omega)
  let average : ℝ :=
    𝔼 omega : SystemSample T,
      if Good side T.card omega then L omega else 0
  refine ⟨average, ?_, ?_⟩
  · have hGap := good_expect_selected_gap_ge T P hT hprime hk side
    have hHeavy :
        (1 / 8 - 12 / (T.card : ℝ)) * BpOrdered p T ≤
          𝔼 omega : SystemSample T,
            if Good side T.card omega then
              Real.log p * (selectedPadicSlack T p tauHeavy omega : ℝ)
            else 0 := by
      simpa only [side] using hHeavyGood
    have hpoint (omega : SystemSample T) :
        (if Good side T.card omega then
            (AweightOrdered (S omega) - BPOrdered P (S omega)) +
              Real.log p * (selectedPadicSlack T p tauHeavy omega : ℝ)
          else 0) ≤
        (if Good side T.card omega then L omega else 0) := by
      by_cases hg : Good side T.card omega
      · simp only [hg, if_true]
        dsimp only [L]
        have hpLog : 0 ≤ Real.log p :=
          Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp.ne_zero))
        have hheavyTerm := mul_le_mul_of_nonneg_left (hsigmaHeavy omega) hpLog
        have hother : 0 ≤
            ∑ q ∈ P.erase p,
              Real.log q * pSlack q (S omega) (sigma omega q) := by
          apply Finset.sum_nonneg
          intro q hq
          have hqP := (Finset.mem_erase.mp hq).2
          exact mul_nonneg
            (Real.log_nonneg (by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hprime q hqP).ne_zero)))
            (hsigmaNonneg omega q hqP)
        have hsplit :
            ∑ q ∈ P, Real.log q * pSlack q (S omega) (sigma omega q) =
              Real.log p * pSlack p (S omega) (sigma omega p) +
                ∑ q ∈ P.erase p,
                  Real.log q * pSlack q (S omega) (sigma omega q) := by
          rw [← Finset.add_sum_erase _ _ hpP]
        rw [hsplit]
        linarith
      · simp [hg]
    have hExpectPoint :
        (𝔼 omega : SystemSample T,
          if Good side T.card omega then
            (AweightOrdered (S omega) - BPOrdered P (S omega)) +
              Real.log p * (selectedPadicSlack T p tauHeavy omega : ℝ)
          else 0) ≤ average := by
      dsimp only [average]
      exact Finset.expect_le_expect fun omega _ => hpoint omega
    have hsplitExpect :
        (𝔼 omega : SystemSample T,
          if Good side T.card omega then
            (AweightOrdered (S omega) - BPOrdered P (S omega)) +
              Real.log p * (selectedPadicSlack T p tauHeavy omega : ℝ)
          else 0) =
        (𝔼 omega : SystemSample T,
          if Good side T.card omega then
            AweightOrdered (S omega) - BPOrdered P (S omega) else 0) +
        (𝔼 omega : SystemSample T,
          if Good side T.card omega then
            Real.log p * (selectedPadicSlack T p tauHeavy omega : ℝ) else 0) := by
      rw [← Finset.expect_add_distrib]
      apply Finset.expect_congr rfl
      intro omega homega
      by_cases hg : Good side T.card omega <;> simp [hg]
    have hAZ : 0 ≤ AweightOrdered T - BPOrdered P T := by
      rw [← sum_ambientGapWeight_eq]
      apply Finset.sum_nonneg
      intro e he
      let ee : T × T :=
        (⟨e.1, (Finset.mem_offDiag.mp he).1⟩,
          ⟨e.2, (Finset.mem_offDiag.mp he).2.1⟩)
      exact ambientGapWeight_nonneg T P hT hprime ee
        (fun h => (Finset.mem_offDiag.mp he).2.2 (congrArg Subtype.val h))
    have hBP : 0 ≤ BPOrdered P T := by
      unfold BPOrdered BpOrdered
      apply Finset.sum_nonneg
      intro q hq
      apply Finset.sum_nonneg
      intro e he
      exact mul_nonneg (by positivity)
        (Real.log_nonneg (by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hprime q hq).ne_zero)))
    have hAlpha : (1 / 8 : ℝ) ≤ 3 / 16 - 12 / (T.card : ℝ) := by
      have hkR : (192 : ℝ) < T.card := by exact_mod_cast hkLarge
      have hkpos : (0 : ℝ) < T.card := by positivity
      have hsmall : 12 / (T.card : ℝ) < (1 / 16 : ℝ) := by
        apply (div_lt_iff₀ hkpos).mpr
        nlinarith
      nlinarith
    have hBeta : (1 / 16 : ℝ) ≤ 1 / 8 - 12 / (T.card : ℝ) := by
      have hkR : (192 : ℝ) < T.card := by exact_mod_cast hkLarge
      have hkpos : (0 : ℝ) < T.card := by positivity
      have hsmall : 12 / (T.card : ℝ) < (1 / 16 : ℝ) := by
        apply (div_lt_iff₀ hkpos).mpr
        nlinarith
      nlinarith
    have hInv : (1 / (16 * (P.card : ℝ)) : ℝ) ≤ 1 / 8 := by
      have hr1 : (1 : ℝ) ≤ P.card := by
        exact_mod_cast (Finset.one_le_card.mpr hPnonempty)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * P.card)).mpr
      nlinarith
    have hGapPart :
        (1 / (16 * (P.card : ℝ))) * (AweightOrdered T - BPOrdered P T) ≤
          (3 / 16 - 12 / (T.card : ℝ)) *
            (AweightOrdered T - BPOrdered P T) :=
      mul_le_mul_of_nonneg_right (hInv.trans hAlpha) hAZ
    have hAvgHeavy : BPOrdered P T / (P.card : ℝ) ≤ BpOrdered p T := hpHeavy
    have hHeavyPart :
        (1 / 16) * (BPOrdered P T / (P.card : ℝ)) ≤
          (1 / 8 - 12 / (T.card : ℝ)) * BpOrdered p T := by
      calc
        _ ≤ (1 / 16) * BpOrdered p T :=
          mul_le_mul_of_nonneg_left hAvgHeavy (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_right hBeta (by
          exact le_trans (div_nonneg hBP hr.le) hAvgHeavy)
    rw [hsplitExpect] at hExpectPoint
    have hcombined := add_le_add hGap hHeavy
    have hid :
        (1 / (16 * (P.card : ℝ))) * AweightOrdered T =
          (1 / (16 * (P.card : ℝ))) *
              (AweightOrdered T - BPOrdered P T) +
            (1 / 16) * (BPOrdered P T / (P.card : ℝ)) := by
      field_simp
      ring
    rw [hid]
    exact (add_le_add hGapPart hHeavyPart).trans (hcombined.trans hExpectPoint)
  · have hpointUpper (omega : SystemSample T)
        (hg : Good side T.card omega) :
        L omega ≤
          (48 * (P.card : ℝ) / (T.card : ℝ)) * AweightOrdered T := by
      have hcardS8 : T.card ≤ 8 * (S omega).card := by
        exact card_le_eight_mul_selectedNat_card_of_good side omega hg
      have hcardS2 : 2 ≤ (S omega).card := by omega
      have hmetric :=
        card_mul_sum_log_involutionCost_le_six_card_mul_AweightOrdered
          (S omega) (hSpos omega) hcardS2 P hprime (sigma omega)
          (hsigmaInv omega)
      rw [← hidentity omega] at hmetric
      have hLnonneg : 0 ≤ L omega := by
        rw [hidentity omega]
        apply Finset.sum_nonneg
        intro q hq
        positivity
      have hASnonneg : 0 ≤ AweightOrdered (S omega) := by
        rw [AweightOrdered]
        apply Finset.sum_nonneg
        intro e he
        apply Real.log_nonneg
        have he' := Finset.mem_offDiag.mp he
        have htwo := Normalized.two_le_normalizedSum
          (hSpos omega e.1 he'.1) (hSpos omega e.2 he'.2.1) he'.2.2
        exact_mod_cast (show 1 ≤ Normalized.normalizedSum e.1 e.2 by omega)
      have hAT := AweightOrdered_mono_of_subset (hSsub omega) hT
      have hkR : (0 : ℝ) < T.card := by positivity
      have hcardR : (T.card : ℝ) ≤ 8 * ((S omega).card : ℝ) := by
        exact_mod_cast hcardS8
      have hkL : (T.card : ℝ) * L omega ≤
          48 * (P.card : ℝ) * AweightOrdered (S omega) := by
        have hfirst := mul_le_mul_of_nonneg_right hcardR hLnonneg
        have hsecond := mul_le_mul_of_nonneg_left hmetric (by norm_num : (0 : ℝ) ≤ 8)
        nlinarith
      have hkLAT : (T.card : ℝ) * L omega ≤
          48 * (P.card : ℝ) * AweightOrdered T :=
        hkL.trans (by gcongr)
      have hdiv : L omega ≤
          (48 * (P.card : ℝ) * AweightOrdered T) / (T.card : ℝ) := by
        apply (le_div_iff₀ hkR).mpr
        simpa [mul_comm] using hkLAT
      calc
        L omega ≤ (48 * (P.card : ℝ) * AweightOrdered T) /
            (T.card : ℝ) := hdiv
        _ = (48 * (P.card : ℝ) / (T.card : ℝ)) * AweightOrdered T := by ring
    have hAvg48 : average ≤
        (48 * (P.card : ℝ) / (T.card : ℝ)) * AweightOrdered T := by
      dsimp only [average]
      apply Finset.expect_le (s := (Finset.univ : Finset (SystemSample T)))
        (Finset.univ_nonempty)
      intro omega homega
      by_cases hg : Good side T.card omega
      · simpa [hg] using hpointUpper omega hg
      · simp [hg]
        have hApos := (AweightOrdered_pos T hT hcard2).le
        positivity
    exact hAvg48.trans (by
      have hApos := (AweightOrdered_pos T hT hcard2).le
      have hcoeff : 48 * (P.card : ℝ) / (T.card : ℝ) ≤
          96 * (P.card : ℝ) / (T.card : ℝ) := by
        have hkR : (0 : ℝ) < T.card := by positivity
        apply (div_le_div_iff_of_pos_right hkR).mpr
        nlinarith [hr.le]
      exact mul_le_mul_of_nonneg_right hcoeff hApos)

/-- Exact positive-set coefficient needed before erasing a possible zero. -/
theorem positive_card_le_1536_support_sq
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) (hcard : 2 ≤ T.card) :
    T.card ≤ 1536 * (addPrimeSupport T).card ^ 2 := by
  by_cases hsmall : T.card ≤ 192
  · exact small_positive_card_le_1536_support_sq T hT hcard hsmall
  · exact card_le_1536_support_sq_of_expectationSandwich T hT hcard
      (globalExpectationGlue T hT (Nat.lt_of_not_ge hsmall))

/-- Fully concrete finite square-root bound for arbitrary natural-number
finsets.  Removing zero changes `1536` to `1537`, which is then weakened to
the round constant `1600`. -/
theorem finite_quadratic_prime_support_bound_integrated
    (A : Finset ℕ) (hcard : 2 < A.card) :
    A.card ≤ 1600 * (addPrimeSupport A).card ^ 2 := by
  have h1537 := card_le_succ_mul_support_sq_of_positive_bound
    1536 positive_card_le_1536_support_sq A hcard
  exact h1537.trans (Nat.mul_le_mul_right _ (by norm_num : 1537 ≤ 1600))

end

end Erdos126
