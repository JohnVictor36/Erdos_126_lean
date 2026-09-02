import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Erdos126

/-- Any eventual positive constant multiple of `sqrt n` dominates `log n` by an
unbounded factor. This is the analytic implication needed after proving the
finite combinatorial lower bound for Erdős problem 126. -/
theorem tendsto_div_log_atTop_of_eventually_sqrt_le
    (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ᶠ n : ℕ in atTop, c * Real.sqrt (n : ℝ) ≤ (f n : ℝ)) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop := by
  have hlog_div_sqrt :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by exact one_half_pos)).tendsto_div_nhds_zero
  have hlog_div_sqrt_pos :
      ∀ᶠ x : ℝ in atTop, 0 < Real.log x / Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.sqrt_pos.2 (zero_lt_one.trans hx))
  have hsqrt_div_log_real :
      Tendsto (fun x : ℝ => Real.sqrt x / Real.log x) atTop atTop := by
    have hright :
        Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlog_div_sqrt, hlog_div_sqrt_pos⟩
    convert tendsto_inv_nhdsGT_zero.comp hright using 1
    ext x
    change Real.sqrt x / Real.log x = (Real.log x / Real.sqrt x)⁻¹
    exact (inv_div (Real.log x) (Real.sqrt x)).symm
  have hsqrt_div_log_nat :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / Real.log n) atTop atTop :=
    hsqrt_div_log_real.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ (Tendsto.const_mul_atTop hc hsqrt_div_log_nat)
  filter_upwards [hf, eventually_gt_atTop 1] with n hfn hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hn)
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hlog).mpr hfn

/-- Pointwise square-root lower bounds imply the conclusion of Erdős problem 126. -/
theorem tendsto_div_log_atTop_of_sqrt_le
    (f : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ n : ℕ, c * Real.sqrt (n : ℝ) ≤ (f n : ℝ)) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop :=
  tendsto_div_log_atTop_of_eventually_sqrt_le f c hc (Eventually.of_forall hf)

end Erdos126
