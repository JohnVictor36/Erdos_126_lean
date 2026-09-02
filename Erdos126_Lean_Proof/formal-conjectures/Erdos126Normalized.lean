import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

/-!
# The normalized sum--difference pair for Erdős problem 126

This file isolates the elementary arithmetic normalization used in the proposed
square-root lower bound.  Dividing two positive integers by their gcd gives a
coprime pair `x`, `y`.  If both reduced integers are odd, one further divides
their sum and distance by two.  The resulting two integers are coprime.
-/

namespace Erdos126.Normalized

/-- The left member of the pair after dividing by the gcd. -/
def reducedLeft (a b : ℕ) : ℕ := a / a.gcd b

/-- The right member of the pair after dividing by the gcd. -/
def reducedRight (a b : ℕ) : ℕ := b / a.gcd b

/-- Whether the reduced pair has a common extra factor two in its sum and distance. -/
def needsTwo (a b : ℕ) : Prop := Odd (reducedLeft a b) ∧ Odd (reducedRight a b)

instance (a b : ℕ) : Decidable (needsTwo a b) := by
  unfold needsTwo
  infer_instance

/-- The gcd, enlarged by two exactly when the reduced pair is odd--odd. -/
def normalizer (a b : ℕ) : ℕ :=
  (if needsTwo a b then 2 else 1) * a.gcd b

/-- The normalized sum. -/
def normalizedSum (a b : ℕ) : ℕ := (a + b) / normalizer a b

/-- The normalized absolute difference. -/
def normalizedDist (a b : ℕ) : ℕ := Nat.dist a b / normalizer a b

private lemma odd_iff_factorization_two_eq_zero {n : ℕ} (hn : 0 < n) :
    Odd n ↔ n.factorization 2 = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  simp [Nat.prime_two, hn.ne', ← Nat.not_even_iff_odd, even_iff_two_dvd]

/-- On positive inputs, `needsTwo` is equivalent to equality of the two 2-adic orders. -/
lemma needsTwo_iff_factorization_two_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    needsTwo a b ↔ a.factorization 2 = b.factorization 2 := by
  let g := a.gcd b
  let x := reducedLeft a b
  let y := reducedRight a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hx : 0 < x := by
    exact Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
  have hy : 0 < y := by
    exact Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
  have ha' : a = g * x := by
    simp only [g, x, reducedLeft]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hb' : b = g * y := by
    simp only [g, y, reducedRight]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have hcop : x.Coprime y := Nat.coprime_div_gcd_div_gcd hg
  have hmin : min (x.factorization 2) (y.factorization 2) = 0 := by
    have hfac := congrArg (fun f : ℕ →₀ ℕ ↦ f 2) (Nat.factorization_gcd hx.ne' hy.ne')
    rw [hcop.gcd_eq_one] at hfac
    simpa using hfac.symm
  have hfa : a.factorization 2 = g.factorization 2 + x.factorization 2 := by
    rw [ha', Nat.factorization_mul hg.ne' hx.ne']
    rfl
  have hfb : b.factorization 2 = g.factorization 2 + y.factorization 2 := by
    rw [hb', Nat.factorization_mul hg.ne' hy.ne']
    rfl
  rw [needsTwo, odd_iff_factorization_two_eq_zero hx,
    odd_iff_factorization_two_eq_zero hy, hfa, hfb]
  rcases Nat.min_eq_zero_iff.mp hmin with hx0 | hy0 <;> omega

/-- This is the `2^ε gcd(a,b)` description of the normalizer, with `ε` determined
by equality of the two 2-adic orders. -/
lemma normalizer_eq_if_factorization_two_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    normalizer a b = (if a.factorization 2 = b.factorization 2 then 2 else 1) * a.gcd b := by
  by_cases htwo : needsTwo a b
  · have hv := (needsTwo_iff_factorization_two_eq ha hb).mp htwo
    simp [normalizer, htwo, hv]
  · have hv : a.factorization 2 ≠ b.factorization 2 :=
      fun hv ↦ htwo ((needsTwo_iff_factorization_two_eq ha hb).mpr hv)
    simp [normalizer, htwo, hv]

private lemma odd_sum {x y : ℕ} (hcop : x.Coprime y) (hnot : ¬(Odd x ∧ Odd y)) :
    Odd (x + y) := by
  have hnotEvenEven : ¬(Even x ∧ Even y) := by
    rintro ⟨hx, hy⟩
    have h21 : (2 : ℕ) = 1 := Nat.eq_one_of_dvd_coprimes hcop hx.two_dvd hy.two_dvd
    omega
  rcases Nat.even_or_odd x with hx | hx
  · have hy : Odd y := Nat.not_even_iff_odd.mp fun hy ↦ hnotEvenEven ⟨hx, hy⟩
    exact hx.add_odd hy
  · have hy : Even y := Nat.not_odd_iff_even.mp fun hy ↦ hnot ⟨hx, hy⟩
    exact hx.add_even hy

/-- For a coprime pair of opposite parity, its sum and absolute difference are coprime. -/
lemma coprime_add_dist_of_not_both_odd {x y : ℕ} (hcop : x.Coprime y)
    (hnot : ¬(Odd x ∧ Odd y)) : (x + y).Coprime (Nat.dist x y) := by
  have hsumOdd : Odd (x + y) := odd_sum hcop hnot
  rcases le_total x y with hxy | hyx
  · have hcopSumX : (x + y).Coprime x := Nat.coprime_self_add_left.mpr hcop.symm
    have hcopSumTwo : (x + y).Coprime 2 := Nat.coprime_two_right.mpr hsumOdd
    have hcopProd : (x + y).Coprime (2 * x) :=
      Nat.coprime_mul_iff_right.mpr ⟨hcopSumTwo, hcopSumX⟩
    have hsub := (Nat.coprime_self_sub_right (by omega : 2 * x ≤ x + y)).mpr hcopProd
    rw [Nat.dist_eq_sub_of_le hxy]
    convert hsub using 1
    all_goals omega
  · have hcopSumY : (x + y).Coprime y := Nat.coprime_add_self_left.mpr hcop
    have hcopSumTwo : (x + y).Coprime 2 := Nat.coprime_two_right.mpr hsumOdd
    have hcopProd : (x + y).Coprime (2 * y) :=
      Nat.coprime_mul_iff_right.mpr ⟨hcopSumTwo, hcopSumY⟩
    have hsub := (Nat.coprime_self_sub_right (by omega : 2 * y ≤ x + y)).mpr hcopProd
    rw [Nat.dist_eq_sub_of_le_right hyx]
    convert hsub using 1
    all_goals omega

/-- For a coprime odd--odd pair, halving both the sum and distance leaves a coprime pair. -/
lemma coprime_half_add_dist {x y : ℕ} (hcop : x.Coprime y) (hx : Odd x) (hy : Odd y) :
    ((x + y) / 2).Coprime (Nat.dist x y / 2) := by
  have hxmod : x % 2 = 1 := Nat.odd_iff.mp hx
  have hymod : y % 2 = 1 := Nat.odd_iff.mp hy
  rcases le_total x y with hxy | hyx
  · let u := (x + y) / 2
    let d := (y - x) / 2
    have hdle : d ≤ u := by simp only [u, d]; omega
    have hsub : u - d = x := by simp only [u, d]; omega
    have hadd : y = 2 * d + x := by simp only [d]; omega
    have hcopXD : x.Coprime d := by
      have hcopXTwoD : x.Coprime (2 * d) := by
        apply Nat.coprime_add_self_right.mp
        simpa [hadd] using hcop
      exact hcopXTwoD.of_dvd_right (dvd_mul_left d 2)
    have hcopSub : (u - d).Coprime d := hsub.symm ▸ hcopXD
    have hcopUD : u.Coprime d := (Nat.coprime_sub_self_left hdle).mp hcopSub
    simpa only [u, d, Nat.dist_eq_sub_of_le hxy] using hcopUD
  · let u := (x + y) / 2
    let d := (x - y) / 2
    have hdle : d ≤ u := by simp only [u, d]; omega
    have hsub : u - d = y := by simp only [u, d]; omega
    have hadd : x = 2 * d + y := by simp only [d]; omega
    have hcopYD : y.Coprime d := by
      have hcopYTwoD : y.Coprime (2 * d) := by
        apply Nat.coprime_add_self_right.mp
        simpa [add_comm, hadd] using hcop.symm
      exact hcopYTwoD.of_dvd_right (dvd_mul_left d 2)
    have hcopSub : (u - d).Coprime d := hsub.symm ▸ hcopYD
    have hcopUD : u.Coprime d := (Nat.coprime_sub_self_left hdle).mp hcopSub
    simpa only [u, d, Nat.dist_eq_sub_of_le_right hyx] using hcopUD

lemma gcd_dvd_normalized_sum (a b : ℕ) : a.gcd b ∣ a + b :=
  dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

lemma gcd_dvd_normalized_dist (a b : ℕ) : a.gcd b ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.dvd_sub_iff_left hab (Nat.gcd_dvd_left a b)).mpr (Nat.gcd_dvd_right a b)
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (Nat.dvd_sub_iff_left hba (Nat.gcd_dvd_right a b)).mpr (Nat.gcd_dvd_left a b)

lemma normalizer_dvd_sum {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) : normalizer a b ∣ a + b := by
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
  by_cases htwo : needsTwo a b
  · have htwo' : Odd x ∧ Odd y := by simpa [needsTwo, x, y] using htwo
    have heven : Even (x + y) := htwo'.1.add_odd htwo'.2
    have hnorm : normalizer a b = 2 * g := by simp [normalizer, htwo, g]
    rw [hnorm, ha', hb', ← mul_add]
    simpa [mul_comm] using mul_dvd_mul_right heven.two_dvd g
  · simpa [normalizer, htwo] using gcd_dvd_normalized_sum a b

lemma normalizer_dvd_dist {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    normalizer a b ∣ Nat.dist a b := by
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
  by_cases htwo : needsTwo a b
  · have htwo' : Odd x ∧ Odd y := by simpa [needsTwo, x, y] using htwo
    have heven : Even (Nat.dist x y) := by
      rcases le_total x y with hxy | hyx
      · rw [Nat.dist_eq_sub_of_le hxy]
        exact Nat.Odd.sub_odd htwo'.2 htwo'.1
      · rw [Nat.dist_eq_sub_of_le_right hyx]
        exact Nat.Odd.sub_odd htwo'.1 htwo'.2
    have hnorm : normalizer a b = 2 * g := by simp [normalizer, htwo, g]
    rw [hnorm, ha', hb', Nat.dist_mul_left]
    simpa [mul_comm] using mul_dvd_mul_right heven.two_dvd g
  · simpa [normalizer, htwo] using gcd_dvd_normalized_dist a b

lemma normalizer_pos {a b : ℕ} (ha : 0 < a) : 0 < normalizer a b := by
  by_cases htwo : needsTwo a b <;>
    simp [normalizer, htwo, Nat.gcd_pos_of_pos_left b ha]

lemma normalizedSum_mul_normalizer {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    normalizedSum a b * normalizer a b = a + b := by
  exact Nat.div_mul_cancel (normalizer_dvd_sum ha hb)

lemma normalizedDist_mul_normalizer {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    normalizedDist a b * normalizer a b = Nat.dist a b := by
  exact Nat.div_mul_cancel (normalizer_dvd_dist ha hb)

lemma normalizedSum_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < normalizedSum a b := by
  exact Nat.div_pos (Nat.le_of_dvd (Nat.add_pos_left ha b) (normalizer_dvd_sum ha hb))
    (normalizer_pos ha)

lemma normalizedDist_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < normalizedDist a b := by
  exact Nat.div_pos (Nat.le_of_dvd (Nat.dist_pos_of_ne hab) (normalizer_dvd_dist ha hb))
    (normalizer_pos ha)

/-- The normalized sum and distance attached to two positive integers are coprime. -/
theorem normalized_coprime {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    (normalizedSum a b).Coprime (normalizedDist a b) := by
  let g := a.gcd b
  let x := reducedLeft a b
  let y := reducedRight a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hcop : x.Coprime y := by
    exact Nat.coprime_div_gcd_div_gcd hg
  have ha' : a = g * x := by
    simp only [g, x, reducedLeft]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hb' : b = g * y := by
    simp only [g, y, reducedRight]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  by_cases htwo : needsTwo a b
  · have htwo' : Odd x ∧ Odd y := by simpa [needsTwo, x, y] using htwo
    have hnorm : normalizer a b = 2 * g := by simp [normalizer, htwo, g]
    have hsum : normalizedSum a b = (x + y) / 2 := by
      rw [normalizedSum, hnorm, ha', hb', ← mul_add]
      rw [mul_comm 2 g, Nat.mul_div_mul_left _ _ hg]
    have hdist : normalizedDist a b = Nat.dist x y / 2 := by
      rw [normalizedDist, hnorm, ha', hb', Nat.dist_mul_left]
      rw [mul_comm 2 g, Nat.mul_div_mul_left _ _ hg]
    rw [hsum, hdist]
    exact coprime_half_add_dist hcop htwo'.1 htwo'.2
  · have htwo' : ¬(Odd x ∧ Odd y) := by simpa [needsTwo, x, y] using htwo
    have hnorm : normalizer a b = g := by simp [normalizer, htwo, g]
    have hsum : normalizedSum a b = x + y := by
      rw [normalizedSum, hnorm, ha', hb', ← mul_add]
      exact Nat.mul_div_cancel_left _ hg
    have hdist : normalizedDist a b = Nat.dist x y := by
      rw [normalizedDist, hnorm, ha', hb', Nat.dist_mul_left]
      exact Nat.mul_div_cancel_left _ hg
    rw [hsum, hdist]
    exact coprime_add_dist_of_not_both_odd hcop htwo'

end Erdos126.Normalized
