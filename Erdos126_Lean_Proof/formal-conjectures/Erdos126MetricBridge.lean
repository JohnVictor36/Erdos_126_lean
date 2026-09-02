import Erdos126Normalized
import Erdos126Metric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
Arithmetic comparisons connecting the normalized pair to the valuation metric.
-/

open scoped BigOperators

namespace Erdos126.Normalized

lemma reducedLeft_pos {a b : ℕ} (ha : 0 < a) : 0 < reducedLeft a b := by
  exact Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b))
    (Nat.gcd_pos_of_pos_left b ha)

lemma reducedRight_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < reducedRight a b := by
  exact Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b))
    (Nat.gcd_pos_of_pos_left b ha)

/-- Express the normalized sum using the two coprime reduced inputs. -/
lemma normalizedSum_eq_reduced {a b : ℕ} (ha : 0 < a) :
    normalizedSum a b =
      if needsTwo a b then (reducedLeft a b + reducedRight a b) / 2
      else reducedLeft a b + reducedRight a b := by
  let g := a.gcd b
  let x := reducedLeft a b
  let y := reducedRight a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have ha' : a = g * x := by
    simp only [g, x, reducedLeft]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hb' : b = g * y := by
    simp only [g, y, reducedRight]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  change normalizedSum a b =
    if needsTwo a b then (x + y) / 2 else x + y
  by_cases htwo : needsTwo a b
  · rw [if_pos htwo]
    have hnorm : normalizer a b = 2 * g := by simp [normalizer, htwo, g]
    rw [normalizedSum, hnorm, ha', hb', ← mul_add]
    rw [mul_comm 2 g, Nat.mul_div_mul_left _ _ hg]
  · rw [if_neg htwo]
    have hnorm : normalizer a b = g := by simp [normalizer, htwo, g]
    rw [normalizedSum, hnorm, ha', hb', ← mul_add]
    exact Nat.mul_div_cancel_left _ hg

/-- The normalized numerator is at most twice the product of the reduced inputs. -/
theorem normalizedSum_le_two_mul_reduced {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    normalizedSum a b ≤ 2 * (reducedLeft a b * reducedRight a b) := by
  let x := reducedLeft a b
  let y := reducedRight a b
  have hx : 1 ≤ x := reducedLeft_pos ha
  have hy : 1 ≤ y := reducedRight_pos ha hb
  have hxmul : x ≤ x * y := le_mul_of_one_le_right (Nat.zero_le x) hy
  have hymul : y ≤ x * y := le_mul_of_one_le_left (Nat.zero_le y) hx
  have hsum : x + y ≤ 2 * (x * y) := by omega
  rw [normalizedSum_eq_reduced ha]
  split_ifs
  · exact (Nat.div_le_self (x + y) 2).trans hsum
  · exact hsum

/-- Distinct positive inputs have normalized numerator at least two. -/
theorem two_le_normalizedSum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    2 ≤ normalizedSum a b := by
  let g := a.gcd b
  let x := reducedLeft a b
  let y := reducedRight a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hx : 0 < x := reducedLeft_pos ha
  have hy : 0 < y := reducedRight_pos ha hb
  have ha' : a = g * x := by
    simp only [g, x, reducedLeft]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hb' : b = g * y := by
    simp only [g, y, reducedRight]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hxy : x ≠ y := by
    intro h
    apply hab
    rw [ha', hb', h]
  rw [normalizedSum_eq_reduced ha]
  by_cases htwo : needsTwo a b
  · rw [if_pos htwo]
    have hodd : Odd x ∧ Odd y := by simpa [x, y, needsTwo] using htwo
    obtain ⟨m, hm⟩ := hodd.1
    obtain ⟨n, hn⟩ := hodd.2
    change 2 ≤ (x + y) / 2
    omega
  · rw [if_neg htwo]
    change 2 ≤ x + y
    omega

/-- Arithmetic-geometric mean lower bound for the normalized numerator. -/
theorem sqrt_reduced_mul_le_normalizedSum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt ((reducedLeft a b : ℝ) * reducedRight a b) ≤ normalizedSum a b := by
  let x := reducedLeft a b
  let y := reducedRight a b
  let u := normalizedSum a b
  have hx : 0 < x := reducedLeft_pos ha
  have hy : 0 < y := reducedRight_pos ha hb
  have hu : 0 < u := normalizedSum_pos ha hb
  change Real.sqrt ((x : ℝ) * y) ≤ (u : ℝ)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  by_cases htwo : needsTwo a b
  · have hodd : Odd x ∧ Odd y := by simpa [x, y, needsTwo] using htwo
    have heven : 2 ∣ x + y := (hodd.1.add_odd hodd.2).two_dvd
    have hu' : u = (x + y) / 2 := by
      simpa [u, x, y, htwo] using normalizedSum_eq_reduced (a := a) (b := b) ha
    have hdouble : 2 * u = x + y := by
      rw [hu', mul_comm]
      exact Nat.div_mul_cancel heven
    have hdoubleR : (2 : ℝ) * u = x + y := by exact_mod_cast hdouble
    nlinarith [sq_nonneg ((x : ℝ) - y)]
  · have hu' : u = x + y := by
      simpa [u, x, y, htwo] using normalizedSum_eq_reduced (a := a) (b := b) ha
    have huR : (u : ℝ) = x + y := by exact_mod_cast hu'
    nlinarith [sq_nonneg ((x : ℝ) - y)]

/-- Logged form of the lower arithmetic comparison. -/
theorem half_log_reduced_mul_le_log_normalizedSum {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    Real.log ((reducedLeft a b : ℝ) * reducedRight a b) / 2 ≤
      Real.log (normalizedSum a b) := by
  have hprod : 0 < (reducedLeft a b : ℝ) * reducedRight a b := by
    positivity [reducedLeft_pos (a := a) (b := b) ha,
      reducedRight_pos (a := a) (b := b) ha hb]
  have hsqrt : 0 < Real.sqrt ((reducedLeft a b : ℝ) * reducedRight a b) :=
    Real.sqrt_pos.2 hprod
  rw [← Real.log_sqrt hprod.le]
  exact Real.log_le_log hsqrt (sqrt_reduced_mul_le_normalizedSum ha hb)

/-- The additive `log 2` budget on every off-diagonal normalized edge. -/
theorem log_two_le_log_normalizedSum {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log 2 ≤ Real.log (normalizedSum a b) := by
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
  exact_mod_cast two_le_normalizedSum ha hb hab

/-- Logged form of the upper arithmetic comparison. -/
theorem log_normalizedSum_le_log_reduced_mul_add_log_two {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    Real.log (normalizedSum a b) ≤
      Real.log ((reducedLeft a b : ℝ) * reducedRight a b) + Real.log 2 := by
  have hu : 0 < (normalizedSum a b : ℝ) := by
    positivity [normalizedSum_pos ha hb]
  have hxy : 0 < (reducedLeft a b : ℝ) * reducedRight a b := by
    positivity [reducedLeft_pos (a := a) (b := b) ha,
      reducedRight_pos (a := a) (b := b) ha hb]
  have hle : (normalizedSum a b : ℝ) ≤
      2 * ((reducedLeft a b : ℝ) * reducedRight a b) := by
    exact_mod_cast normalizedSum_le_two_mul_reduced ha hb
  calc
    Real.log (normalizedSum a b) ≤
        Real.log (2 * ((reducedLeft a b : ℝ) * reducedRight a b)) :=
      Real.log_le_log hu hle
    _ = Real.log ((reducedLeft a b : ℝ) * reducedRight a b) + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxy.ne']
      ring

/-- The prime exponent of the product of the two gcd-reduced inputs is the
distance between the corresponding prime exponents of the original inputs. -/
theorem factorization_reduced_mul_apply {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (p : ℕ) :
    (reducedLeft a b * reducedRight a b).factorization p =
      Nat.dist (a.factorization p) (b.factorization p) := by
  have hleft : reducedLeft a b ≠ 0 := (reducedLeft_pos ha).ne'
  have hright : reducedRight a b ≠ 0 := (reducedRight_pos ha hb).ne'
  rw [Nat.factorization_mul hleft hright]
  rw [reducedLeft, reducedRight,
    Nat.factorization_div (Nat.gcd_dvd_left a b),
    Nat.factorization_div (Nat.gcd_dvd_right a b),
    Nat.factorization_gcd ha.ne' hb.ne']
  change
    (a.factorization p - min (a.factorization p) (b.factorization p)) +
      (b.factorization p - min (a.factorization p) (b.factorization p)) =
        Nat.dist (a.factorization p) (b.factorization p)
  simp only [Nat.dist]
  omega

/-- Multiplicative form of the triangle inequality for the reduced product. -/
theorem reduced_mul_dvd_triangle {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    reducedLeft a c * reducedRight a c ∣
      (reducedLeft a b * reducedRight a b) *
        (reducedLeft b c * reducedRight b c) := by
  have hac : reducedLeft a c * reducedRight a c ≠ 0 :=
    Nat.mul_ne_zero (reducedLeft_pos ha).ne' (reducedRight_pos ha hc).ne'
  have hab : reducedLeft a b * reducedRight a b ≠ 0 :=
    Nat.mul_ne_zero (reducedLeft_pos ha).ne' (reducedRight_pos ha hb).ne'
  have hbc : reducedLeft b c * reducedRight b c ≠ 0 :=
    Nat.mul_ne_zero (reducedLeft_pos hb).ne' (reducedRight_pos hb hc).ne'
  rw [← Nat.factorization_le_iff_dvd hac (Nat.mul_ne_zero hab hbc)]
  intro p
  rw [factorization_reduced_mul_apply ha hc,
    Nat.factorization_mul hab hbc]
  change Nat.dist (a.factorization p) (c.factorization p) ≤
    (reducedLeft a b * reducedRight a b).factorization p +
      (reducedLeft b c * reducedRight b c).factorization p
  rw [
    factorization_reduced_mul_apply ha hb,
    factorization_reduced_mul_apply hb hc]
  exact Nat.dist.triangle_inequality _ _ _

/-- Logged form of the valuation-vector triangle inequality. -/
theorem log_reduced_mul_triangle {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log ((reducedLeft a c : ℝ) * reducedRight a c) ≤
      Real.log ((reducedLeft a b : ℝ) * reducedRight a b) +
        Real.log ((reducedLeft b c : ℝ) * reducedRight b c) := by
  let x := reducedLeft a c * reducedRight a c
  let y := (reducedLeft a b * reducedRight a b) *
    (reducedLeft b c * reducedRight b c)
  have hx : 0 < x := by
    dsimp [x]
    positivity [reducedLeft_pos (a := a) (b := c) ha,
      reducedRight_pos (a := a) (b := c) ha hc]
  have hy : 0 < y := by
    dsimp [y]
    positivity [reducedLeft_pos (a := a) (b := b) ha,
      reducedRight_pos (a := a) (b := b) ha hb,
      reducedLeft_pos (a := b) (b := c) hb,
      reducedRight_pos (a := b) (b := c) hb hc]
  have hxy : x ≤ y := Nat.le_of_dvd hy (reduced_mul_dvd_triangle ha hb hc)
  have hlog : Real.log (x : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hx
    · exact_mod_cast hxy
  have hxcast : (x : ℝ) = (reducedLeft a c : ℝ) * reducedRight a c := by
    simp [x]
  rw [← hxcast]
  calc
    Real.log (x : ℝ) ≤ Real.log (y : ℝ) := hlog
    _ = Real.log ((reducedLeft a b : ℝ) * reducedRight a b) +
        Real.log ((reducedLeft b c : ℝ) * reducedRight b c) := by
      dsimp [y]
      push_cast
      rw [Real.log_mul]
      · positivity [reducedLeft_pos (a := a) (b := b) ha,
          reducedRight_pos (a := a) (b := b) ha hb]
      · positivity [reducedLeft_pos (a := b) (b := c) hb,
          reducedRight_pos (a := b) (b := c) hb hc]

end Erdos126.Normalized

namespace Erdos126

section MatchingCost

variable {ι : Type*} [Fintype ι]

/-- The additive constant on all ordered pairs is at most twice the total
off-diagonal weight, provided there are at least two vertices and every
off-diagonal weight is at least that constant. -/
theorem constant_budget_of_offDiag [DecidableEq ι]
    (w : ι → ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_nonneg : ∀ i j, 0 ≤ w i j)
    (hw_offDiag : ∀ i j, i ≠ j → c ≤ w i j)
    (hcard : 2 ≤ Fintype.card ι) :
    (Finset.univ.sum fun _i : ι ↦ Finset.univ.sum fun _j : ι ↦ c) ≤
      2 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
  let s : Finset ι := Finset.univ
  have hoff :
      ∑ e ∈ s.offDiag, c ≤ ∑ e ∈ s.offDiag, w e.1 e.2 := by
    exact Finset.sum_le_sum fun e he ↦
      hw_offDiag e.1 e.2 (Finset.mem_offDiag.mp he).2.2
  have hsubset : s.offDiag ⊆ s ×ˢ s := by
    intro e he
    have h := Finset.mem_offDiag.mp he
    exact Finset.mem_product.mpr ⟨h.1, h.2.1⟩
  have hsub :
      ∑ e ∈ s.offDiag, w e.1 e.2 ≤ ∑ e ∈ s ×ˢ s, w e.1 e.2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun e _ _ ↦ hw_nonneg e.1 e.2
  have hcount :
      ((s.offDiag.card : ℝ) * c) ≤
        Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
    calc
      (s.offDiag.card : ℝ) * c = ∑ e ∈ s.offDiag, c := by simp
      _ ≤ ∑ e ∈ s.offDiag, w e.1 e.2 := hoff
      _ ≤ ∑ e ∈ s ×ˢ s, w e.1 e.2 := hsub
      _ = Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
        simpa [s] using Finset.sum_product' s s w
  let n : ℝ := Fintype.card ι
  have hn : (2 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : 0 ≤ n := by positivity
  have hfactor : 0 ≤ n * (n - 2) * c := mul_nonneg (mul_nonneg hn0 (by linarith)) hc
  have hcardOff : (s.offDiag.card : ℝ) = n * n - n := by
    rw [Finset.offDiag_card]
    simp only [s, Finset.card_univ, n]
    rw [Nat.cast_sub]
    · norm_cast
    · exact Nat.le_mul_of_pos_left _ (by omega : 0 < Fintype.card ι)
  have hconstEval :
      (Finset.univ.sum fun _i : ι ↦ Finset.univ.sum fun _j : ι ↦ c) =
        n * n * c := by
    simp [n]
    ring
  rw [hcardOff] at hcount
  rw [hconstEval]
  nlinarith

/-- Abstract `6 / N` matching-cost estimate.

The left side is `N` copies of the cost of the permutation. The hypothesis
`hconstant` is exactly the budget needed to absorb the additive constant in
the comparison `w ≤ ρ + c`. In the number-theoretic application, `c = log 2`
and the lower bound `U i j ≥ 2` off the diagonal supplies this budget.
-/
theorem sum_perm_weight_le_six_total
    (w ρ : ι → ι → ℝ) (c : ℝ)
    (htriangle : ∀ i j k, ρ i k ≤ ρ i j + ρ j k)
    (hmetric_le : ∀ i j, ρ i j ≤ 2 * w i j)
    (σ : Equiv.Perm ι)
    (hweight_le : ∀ i, w i (σ i) ≤ ρ i (σ i) + c)
    (hconstant :
      (Finset.univ.sum fun _i : ι ↦ Finset.univ.sum fun _j : ι ↦ c) ≤
        2 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j) :
    (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦ w i (σ i)) ≤
      6 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
  have hweightSum :
      (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦ w i (σ i)) ≤
        (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦ ρ i (σ i)) +
        (Finset.univ.sum fun _i : ι ↦ Finset.univ.sum fun _j : ι ↦ c) := by
    calc
      (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦ w i (σ i)) ≤
          Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦
            ρ i (σ i) + c := by
        exact Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun _j _ ↦ hweight_le i
      _ = (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦ ρ i (σ i)) +
          (Finset.univ.sum fun _i : ι ↦ Finset.univ.sum fun _j : ι ↦ c) := by
        simp only [Finset.sum_add_distrib]
  have hmetricSum :
      (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ ρ i j) ≤
        2 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
    calc
      (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ ρ i j) ≤
          Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦
            (w i j + w i j) := by
        exact Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun j _ ↦ by simpa [two_mul] using hmetric_le i j
      _ = 2 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦ w i j := by
        simp only [Finset.sum_add_distrib]
        ring
  have hperm := sum_perm_le_total_of_triangle ρ htriangle σ
  linarith

/-- The normalized logarithmic edge weight, extended by zero on the diagonal. -/
noncomputable def normalizedLogWeight [DecidableEq ι] (a : ι → ℕ) (i j : ι) : ℝ :=
  if i = j then 0 else Real.log (Normalized.normalizedSum (a i) (a j))

/-- The logarithm of the product of the two gcd-reduced inputs, extended by
zero on the diagonal. This is the valuation-vector distance used in Lemma 4. -/
noncomputable def reducedLogMetric [DecidableEq ι] (a : ι → ℕ) (i j : ι) : ℝ :=
  if i = j then 0 else
    Real.log ((Normalized.reducedLeft (a i) (a j) : ℝ) *
      Normalized.reducedRight (a i) (a j))

/-- The reduced logarithmic weight is nonnegative. -/
theorem reducedLogMetric_nonneg [DecidableEq ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (i j : ι) :
    0 ≤ reducedLogMetric a i j := by
  by_cases hij : i = j
  · simp [reducedLogMetric, hij]
  · rw [reducedLogMetric, if_neg hij]
    apply Real.log_nonneg
    have hleft := Normalized.reducedLeft_pos (a := a i) (b := a j) (ha i)
    have hright := Normalized.reducedRight_pos (a := a i) (b := a j) (ha i) (ha j)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hleft.ne' hright.ne'))

/-- The logarithm of the product of the two gcd-reduced inputs is the weighted
`ℓ¹` distance between their prime-exponent vectors, and hence satisfies the
triangle inequality. The factorization identity and its termwise natural-number
triangle inequality are proved above in `factorization_reduced_mul_apply` and
`reduced_mul_dvd_triangle`. -/
theorem reducedLogMetric_triangle [DecidableEq ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) :
    ∀ i j k, reducedLogMetric a i k ≤
      reducedLogMetric a i j + reducedLogMetric a j k := by
  intro i j k
  by_cases hij : i = j
  · subst j
    simp [reducedLogMetric]
  by_cases hjk : j = k
  · subst k
    simp [reducedLogMetric]
  by_cases hik : i = k
  · rw [reducedLogMetric, if_pos hik]
    exact add_nonneg (reducedLogMetric_nonneg a ha i j)
      (reducedLogMetric_nonneg a ha j k)
  simp only [reducedLogMetric, hij, hjk, hik, if_false]
  exact Normalized.log_reduced_mul_triangle (ha i) (ha j) (ha k)

/-- Concrete `6 / N` permutation-cost bound for normalized pairwise sums.

The triangle inequality for `reducedLogMetric` is proved from prime
factorizations above. Thus all normalization, logarithmic comparison, metric,
and finite constant-budget arguments are discharged in this theorem.
-/
theorem normalizedSum_perm_cost_le_six_total [DecidableEq ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (hainj : Function.Injective a)
    (hcard : 2 ≤ Fintype.card ι) (σ : Equiv.Perm ι) :
    (Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun _j : ι ↦
      normalizedLogWeight a i (σ i)) ≤
      6 * Finset.univ.sum fun i : ι ↦ Finset.univ.sum fun j : ι ↦
        normalizedLogWeight a i j := by
  have hw_nonneg : ∀ i j, 0 ≤ normalizedLogWeight a i j := by
    intro i j
    by_cases hij : i = j
    · simp [normalizedLogWeight, hij]
    · rw [normalizedLogWeight, if_neg hij]
      apply Real.log_nonneg
      have htwo := Normalized.two_le_normalizedSum (ha i) (ha j) (hainj.ne hij)
      exact_mod_cast (show 1 ≤ Normalized.normalizedSum (a i) (a j) by omega)
  have hw_offDiag : ∀ i j, i ≠ j →
      Real.log 2 ≤ normalizedLogWeight a i j := by
    intro i j hij
    rw [normalizedLogWeight, if_neg hij]
    exact Normalized.log_two_le_log_normalizedSum (ha i) (ha j) (hainj.ne hij)
  have hmetric_le : ∀ i j,
      reducedLogMetric a i j ≤ 2 * normalizedLogWeight a i j := by
    intro i j
    by_cases hij : i = j
    · simp [reducedLogMetric, normalizedLogWeight, hij]
    · rw [reducedLogMetric, normalizedLogWeight, if_neg hij, if_neg hij]
      have h := Normalized.half_log_reduced_mul_le_log_normalizedSum (ha i) (ha j)
      linarith
  have hweight_le : ∀ i,
      normalizedLogWeight a i (σ i) ≤
        reducedLogMetric a i (σ i) + Real.log 2 := by
    intro i
    by_cases hi : i = σ i
    · rw [normalizedLogWeight, reducedLogMetric, if_pos hi, if_pos hi, zero_add]
      exact Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    · simpa [normalizedLogWeight, reducedLogMetric, hi] using
        Normalized.log_normalizedSum_le_log_reduced_mul_add_log_two
          (ha i) (ha (σ i))
  have hconstant := constant_budget_of_offDiag
    (normalizedLogWeight a) (Real.log 2) (Real.log_nonneg (by norm_num))
    hw_nonneg hw_offDiag hcard
  exact sum_perm_weight_le_six_total
    (normalizedLogWeight a) (reducedLogMetric a) (Real.log 2)
    (reducedLogMetric_triangle a ha) hmetric_le σ hweight_le hconstant

end MatchingCost

end Erdos126
