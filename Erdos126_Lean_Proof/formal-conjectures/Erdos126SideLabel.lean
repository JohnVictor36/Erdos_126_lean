import Erdos126Padic

/-!
# A threshold-independent side label for the p-adic residue components

At an odd prime, a unit residue `r mod p` is paired by a sum edge with
`-r mod p`.  At `p = 2`, the extra normalization means that the first
nontrivial modulus is `4`, pairing the two odd residues `1` and `3`.
The label below chooses one side from every such pair once and for all.
Consequently it works simultaneously at every positive threshold.
-/

namespace Erdos126.Padic

/-- The first nontrivial residue modulus: `p` at odd primes and `4` at `2`. -/
def sideModulus (p : ℕ) : ℕ := residueModulus p 1

theorem sideModulus_eq (p : ℕ) :
    sideModulus p = if p = 2 then 4 else p := by
  simp [sideModulus, residueModulus]

/-- Orient a nonzero residue by putting the smaller of `r` and `-r` on the
`true` side.  The hypotheses used below ensure that no relevant residue is
self-opposite. -/
def residueSide (q x : ℕ) : Bool :=
  decide (x % q < q - x % q)

/-- Canonical side of a positive integer at a prime.  It depends only on the
unit part modulo `p` (modulo `4` for `p = 2`). -/
def pUnitSide (p a : ℕ) : Bool :=
  residueSide (sideModulus p) (pUnit p a)

theorem residueSide_eq_of_modEq {q x y : ℕ} (hxy : x ≡ y [MOD q]) :
    residueSide q x = residueSide q y := by
  change decide (x % q < q - x % q) =
    decide (y % q < q - y % q)
  change x % q = y % q at hxy
  rw [hxy]

/-- Opposite non-self-opposite residues receive different labels. -/
theorem residueSide_ne_of_dvd_add
    {q x y : ℕ} (hx : ¬q ∣ x) (hnotSame : ¬x ≡ y [MOD q])
    (hadd : q ∣ x + y) :
    residueSide q x ≠ residueSide q y := by
  let r := x % q
  let s := y % q
  have hle : q ≤ r + s := by
    simpa only [r, s] using
      Nat.le_mod_add_mod_of_dvd_add_of_not_dvd hadd hx
  have haddMod := Nat.add_mod_add_of_le_add_mod hle
  have hzero : (x + y) % q = 0 := Nat.dvd_iff_mod_eq_zero.mp hadd
  have hrs : r + s = q := by
    rw [hzero, zero_add] at haddMod
    simpa only [r, s] using haddMod.symm
  have hne : r ≠ s := by
    simpa only [Nat.ModEq, r, s] using hnotSame
  by_cases hr : r < q - r
  · have hs : ¬s < q - s := by omega
    simp [residueSide, r, s, hr, hs]
  · have hs : s < q - s := by omega
    simp [residueSide, r, s, hr, hs]

theorem not_sideModulus_dvd_pUnit
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    ¬sideModulus p ∣ pUnit p a := by
  have hunit : ¬p ∣ pUnit p a :=
    Nat.not_dvd_divMaxPow hp.one_lt (Nat.ne_of_gt ha)
  by_cases hp2 : p = 2
  · subst p
    intro hfour
    apply hunit
    exact (by norm_num [sideModulus, residueModulus] :
      2 ∣ sideModulus 2).trans hfour
  · simpa [sideModulus_eq, hp2] using hunit

/-- Every positive-threshold modulus refines the fixed side modulus. -/
theorem sideModulus_dvd_residueModulus
    {p n : ℕ} (hn : 0 < n) :
    sideModulus p ∣ residueModulus p n := by
  by_cases hp2 : p = 2
  · subst p
    simpa [sideModulus, residueModulus] using
      (Nat.pow_dvd_pow 2 (show 2 ≤ n + 1 by omega))
  · simpa [sideModulus, residueModulus, hp2] using
      (dvd_pow_self p (Nat.ne_of_gt hn))

/-- Reducing a congruence from a positive threshold to the fixed first
modulus preserves equality of the side labels. -/
theorem pUnitSide_eq_of_residueModEq
    {p a b n : ℕ} (hn : 0 < n)
    (hab : pUnit p a ≡ pUnit p b [MOD residueModulus p n]) :
    pUnitSide p a = pUnitSide p b := by
  apply residueSide_eq_of_modEq
  rw [modEq_iff_dvd_dist] at hab ⊢
  exact (sideModulus_dvd_residueModulus hn).trans hab

/-- Reducing an opposite-residue relation from a positive threshold to the
fixed first modulus gives opposite side labels. -/
theorem pUnitSide_ne_of_residueDvdAdd
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hn : 0 < n)
    (hab : residueModulus p n ∣ pUnit p a + pUnit p b) :
    pUnitSide p a ≠ pUnitSide p b := by
  have hdiv : sideModulus p ∣ pUnit p a + pUnit p b :=
    (sideModulus_dvd_residueModulus hn).trans hab
  apply residueSide_ne_of_dvd_add (not_sideModulus_dvd_pUnit hp ha) _ hdiv
  intro hsame
  exact pUnit_not_same_and_opposite
    (u := pUnit p b) (n := 1) hp ha (by omega)
      ⟨hsame.symm, by simpa only [sideModulus, add_comm] using hdiv⟩

/-- Every positive normalized sum-threshold edge joins opposite canonical
sides.  The label is independent of the threshold `n`. -/
theorem pUnitSide_ne_of_normalisedSumVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hab : n ≤ normalisedSumVal p a b) :
    pUnitSide p a ≠ pUnitSide p b := by
  have hres := (normalisedSumVal_threshold_iff hp ha hb hn).mp hab
  exact pUnitSide_ne_of_residueDvdAdd hp ha hn hres.2

/-- Every positive normalized difference-threshold edge joins equal
canonical sides. -/
theorem pUnitSide_eq_of_normalisedDiffVal_threshold
    {p a b n : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (hn : 0 < n)
    (hab : n ≤ normalisedDiffVal p a b) :
    pUnitSide p a = pUnitSide p b := by
  have hres := (normalisedDiffVal_threshold_iff hp ha hb hne hn).mp hab
  exact pUnitSide_eq_of_residueModEq hn hres.2

/-- A single global flip reverses all labels simultaneously. -/
def flippedPUnitSide (flip : Bool) (p a : ℕ) : Bool :=
  xor (pUnitSide p a) flip

theorem flippedPUnitSide_ne_of_normalisedSumVal_threshold
    {flip : Bool} {p a b n : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hab : n ≤ normalisedSumVal p a b) :
    flippedPUnitSide flip p a ≠ flippedPUnitSide flip p b := by
  have h := pUnitSide_ne_of_normalisedSumVal_threshold hp ha hb hn hab
  cases flip <;> cases hpa : pUnitSide p a <;>
    cases hpb : pUnitSide p b <;> simp_all [flippedPUnitSide]

theorem flippedPUnitSide_eq_of_normalisedDiffVal_threshold
    {flip : Bool} {p a b n : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (hn : 0 < n)
    (hab : n ≤ normalisedDiffVal p a b) :
    flippedPUnitSide flip p a = flippedPUnitSide flip p b := by
  rw [flippedPUnitSide, flippedPUnitSide,
    pUnitSide_eq_of_normalisedDiffVal_threshold hp ha hb hne hn hab]

/-- Therefore one flipped side is an independent set in every positive
normalized sum-threshold graph, simultaneously for all thresholds. -/
theorem not_normalisedSumVal_threshold_of_same_flipped_side
    {flip : Bool} {p a b n : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n)
    (haSide : flippedPUnitSide flip p a = true)
    (hbSide : flippedPUnitSide flip p b = true) :
    ¬n ≤ normalisedSumVal p a b := by
  intro hab
  have hne := flippedPUnitSide_ne_of_normalisedSumVal_threshold
    (flip := flip) hp ha hb hn hab
  exact hne (haSide.trans hbSide.symm)

/-- One of the two global flips retains at least half of any finite set.
Together with the previous theorem, that one choice selects a whole side of
every residue component at every positive threshold. -/
theorem exists_global_flip_card
    (T : Finset ℕ) (p : ℕ) :
    ∃ flip : Bool,
      T.card ≤ 2 * (T.filter fun a =>
        flippedPUnitSide flip p a = true).card := by
  let A := T.filter fun a => pUnitSide p a = true
  let B := T.filter fun a => pUnitSide p a = false
  have hpart : A.card + B.card = T.card := by
    have h := Finset.card_filter_add_card_filter_not (s := T)
      (fun a => pUnitSide p a = true)
    simpa only [A, B, Bool.not_eq_true] using h
  by_cases hBA : B.card ≤ A.card
  · refine ⟨false, ?_⟩
    have hfilter :
        (T.filter fun a => flippedPUnitSide false p a = true) = A := by
      ext a
      simp [A, flippedPUnitSide]
    rw [hfilter, ← hpart]
    omega
  · refine ⟨true, ?_⟩
    have hfilter :
        (T.filter fun a => flippedPUnitSide true p a = true) = B := by
      ext a
      cases hside : pUnitSide p a <;> simp [B, flippedPUnitSide, hside]
    rw [hfilter, ← hpart]
    omega

end Erdos126.Padic
