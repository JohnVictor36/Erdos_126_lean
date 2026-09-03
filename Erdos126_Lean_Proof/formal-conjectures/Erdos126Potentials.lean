import Erdos126Factorization
import Erdos126Padic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global logarithmic potentials for Erdős problem 126

The ordered versions use `Finset.offDiag`; the unadorned versions use one
orientation, selected by `<`.  The ordered definitions are the convenient
interface to the p-adic involution theorem.
-/

namespace Erdos126

open scoped BigOperators

noncomputable section

/-- One orientation of each off-diagonal pair. -/
def unorderedEdges (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  T.offDiag.filter fun e => e.1 < e.2

/-- Unordered logarithmic normalized-sum potential. -/
def Aweight (T : Finset ℕ) : ℝ :=
  ∑ e ∈ unorderedEdges T,
    Real.log (Normalized.normalizedSum e.1 e.2)

/-- Ordered logarithmic normalized-sum potential. -/
def AweightOrdered (T : Finset ℕ) : ℝ :=
  ∑ e ∈ T.offDiag,
    Real.log (Normalized.normalizedSum e.1 e.2)

/-- Unordered logarithmic normalized-distance potential. -/
def Bweight (T : Finset ℕ) : ℝ :=
  ∑ e ∈ unorderedEdges T,
    Real.log (Normalized.normalizedDist e.1 e.2)

/-- Ordered logarithmic normalized-distance potential. -/
def BweightOrdered (T : Finset ℕ) : ℝ :=
  ∑ e ∈ T.offDiag,
    Real.log (Normalized.normalizedDist e.1 e.2)

/-- The contribution of one prime to the unordered distance potential. -/
def Bp (p : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ e ∈ unorderedEdges T,
    (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) * Real.log p

/-- The contribution of one prime to the ordered distance potential. -/
def BpOrdered (p : ℕ) (T : Finset ℕ) : ℝ :=
  ∑ e ∈ T.offDiag,
    (padicValNat p (Normalized.normalizedDist e.1 e.2) : ℝ) * Real.log p

/-- The part of the unordered distance potential supported on `P`. -/
def BP (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Bp p T

/-- The part of the ordered distance potential supported on `P`. -/
def BPOrdered (P : Finset ℕ) (T : Finset ℕ) : ℝ :=
  ∑ p ∈ P, BpOrdered p T

/-- Archimedean gap on one edge, written before normalization. -/
def edgeGap (a b : ℕ) : ℝ :=
  Real.log (((a + b : ℕ) : ℝ) / (Nat.dist a b : ℝ))

lemma normalizedDist_lt_normalizedSum {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (_hab : a ≠ b) :
    Normalized.normalizedDist a b < Normalized.normalizedSum a b := by
  have hn := Normalized.normalizer_pos (a := a) (b := b) ha
  have hdist : Nat.dist a b < a + b := by
    rcases le_total a b with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hle]
      omega
  apply (Nat.mul_lt_mul_right hn).mp
  rw [Normalized.normalizedDist_mul_normalizer ha hb,
    Normalized.normalizedSum_mul_normalizer ha hb]
  exact hdist

/-- The normalized logarithmic gap is the logarithm of the original
sum-to-distance ratio. -/
lemma log_normalizedSum_sub_log_normalizedDist_eq_edgeGap
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Real.log (Normalized.normalizedSum a b) -
        Real.log (Normalized.normalizedDist a b) = edgeGap a b := by
  have hU : (Normalized.normalizedSum a b : ℝ) ≠ 0 := by
    exact_mod_cast (Normalized.normalizedSum_pos ha hb).ne'
  have hD : (Normalized.normalizedDist a b : ℝ) ≠ 0 := by
    exact_mod_cast (Normalized.normalizedDist_pos ha hb hab).ne'
  have hN : (Normalized.normalizer a b : ℝ) ≠ 0 := by
    exact_mod_cast (Normalized.normalizer_pos (a := a) (b := b) ha).ne'
  have hsum : (Normalized.normalizedSum a b : ℝ) *
      Normalized.normalizer a b = a + b := by
    exact_mod_cast Normalized.normalizedSum_mul_normalizer ha hb
  have hdist : (Normalized.normalizedDist a b : ℝ) *
      Normalized.normalizer a b = Nat.dist a b := by
    exact_mod_cast Normalized.normalizedDist_mul_normalizer ha hb
  rw [← Real.log_div hU hD]
  unfold edgeGap
  congr 1
  have hdist0 : (Nat.dist a b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.dist_pos_of_ne hab).ne'
  apply (div_eq_div_iff hD hdist0).mpr
  calc
    (Normalized.normalizedSum a b : ℝ) * Nat.dist a b =
        Normalized.normalizedSum a b *
          (Normalized.normalizedDist a b * Normalized.normalizer a b) := by
      rw [hdist]
    _ = (Normalized.normalizedSum a b * Normalized.normalizer a b) *
          Normalized.normalizedDist a b := by ring
    _ = ((a : ℝ) + b) * Normalized.normalizedDist a b := by
      exact congrArg (fun z : ℝ => z * Normalized.normalizedDist a b) hsum
    _ = (((a + b : ℕ) : ℝ) * Normalized.normalizedDist a b) := by
      norm_num

lemma edgeGap_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < edgeGap a b := by
  rw [← log_normalizedSum_sub_log_normalizedDist_eq_edgeGap ha hb hab]
  have hD : 0 < (Normalized.normalizedDist a b : ℝ) := by
    exact_mod_cast Normalized.normalizedDist_pos ha hb hab
  have hU : 0 < (Normalized.normalizedSum a b : ℝ) := by
    exact_mod_cast Normalized.normalizedSum_pos ha hb
  have hlt : (Normalized.normalizedDist a b : ℝ) <
      Normalized.normalizedSum a b := by
    exact_mod_cast normalizedDist_lt_normalizedSum ha hb hab
  exact sub_pos.mpr <| Real.strictMonoOn_log hD hU hlt

/-- The global archimedean slack is an edgewise sum of positive gaps. -/
theorem Aweight_sub_Bweight_eq_sum_edgeGap
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) :
    Aweight T - Bweight T = ∑ e ∈ unorderedEdges T, edgeGap e.1 e.2 := by
  rw [Aweight, Bweight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
  exact log_normalizedSum_sub_log_normalizedDist_eq_edgeGap
    (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2

theorem Aweight_sub_Bweight_pos
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (hcard : 2 ≤ T.card) :
    0 < Aweight T - Bweight T := by
  rw [Aweight_sub_Bweight_eq_sum_edgeGap T hT]
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < T.card by omega)
  have hlt : a < b ∨ b < a := lt_or_gt_of_ne hab
  rcases hlt with hlt | hlt
  · apply Finset.sum_pos'
    · intro e he
      have he' := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
      exact (edgeGap_pos (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2).le
    · refine ⟨(a, b), ?_, edgeGap_pos (hT a ha) (hT b hb) hab⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, hlt⟩
  · apply Finset.sum_pos'
    · intro e he
      have he' := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
      exact (edgeGap_pos (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2).le
    · refine ⟨(b, a), ?_, edgeGap_pos (hT b hb) (hT a ha) hab.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hb, ha, hab.symm⟩, hlt⟩

/-- A partial sum of the prime-factor logarithm over any finite set of primes
is at most the whole logarithm. -/
theorem sum_padicValNat_log_le_log
    {U : ℕ} (_hU : 0 < U) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, (padicValNat p U : ℝ) * Real.log p) ≤ Real.log U := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ P, (padicValNat p U : ℝ) * Real.log p) ≤
    ∑ p ∈ U.primeFactors, (U.factorization p : ℝ) * Real.log p
  let I := P ∩ U.primeFactors
  have hP_eq : (∑ p ∈ P, (padicValNat p U : ℝ) * Real.log p) =
      ∑ p ∈ I, (padicValNat p U : ℝ) * Real.log p := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro p hpP hpI
    have hpU : p ∉ U.primeFactors := by
      simpa [I, hpP] using hpI
    have hfac : U.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hpU
    rw [← Nat.factorization_def U (hprime p hpP), hfac]
    simp
  rw [hP_eq]
  calc
    (∑ p ∈ I, (padicValNat p U : ℝ) * Real.log p) =
        ∑ p ∈ I, (U.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.factorization_def U
        (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).2)]
    _ ≤ ∑ p ∈ U.primeFactors, (U.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
      intro p hpU hpI
      positivity [Real.log_natCast_nonneg]

/-- Restricting the distance factorization to a finite prime set only lowers
the unordered distance potential. -/
theorem BP_le_Bweight
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    BP P T ≤ Bweight T := by
  simp only [BP, Bp, Bweight]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  have he' := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
  exact sum_padicValNat_log_le_log
    (Normalized.normalizedDist_pos (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2)
    P hprime

/-- Ordered version of `BP_le_Bweight`. -/
theorem BPOrdered_le_BweightOrdered
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    BPOrdered P T ≤ BweightOrdered T := by
  simp only [BPOrdered, BpOrdered, BweightOrdered]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  have he' := Finset.mem_offDiag.mp he
  exact sum_padicValNat_log_le_log
    (Normalized.normalizedDist_pos (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2)
    P hprime

theorem Bweight_sub_BP_nonneg
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    0 ≤ Bweight T - BP P T :=
  sub_nonneg.mpr (BP_le_Bweight T hT P hprime)

theorem BweightOrdered_sub_BPOrdered_nonneg
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    0 ≤ BweightOrdered T - BPOrdered P T :=
  sub_nonneg.mpr (BPOrdered_le_BweightOrdered T hT P hprime)

/-- The three nonnegative pieces in the global argument. -/
def Xpotential (T : Finset ℕ) : ℝ := Aweight T - Bweight T
def Ypotential (P : Finset ℕ) (T : Finset ℕ) : ℝ := Bweight T - BP P T
def Zpotential (P : Finset ℕ) (T : Finset ℕ) : ℝ := BP P T

theorem X_add_Y_add_Z (P : Finset ℕ) (T : Finset ℕ) :
    Xpotential T + Ypotential P T + Zpotential P T = Aweight T := by
  simp only [Xpotential, Ypotential, Zpotential]
  ring

theorem Aweight_eq_X_add_Y_add_Z (P : Finset ℕ) (T : Finset ℕ) :
    Aweight T = Xpotential T + Ypotential P T + Zpotential P T :=
  (X_add_Y_add_Z P T).symm

theorem Xpotential_nonneg
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) :
    0 ≤ Xpotential T := by
  rw [Xpotential, Aweight_sub_Bweight_eq_sum_edgeGap T hT]
  exact Finset.sum_nonneg fun e he => by
    have he' := Finset.mem_offDiag.mp (Finset.mem_filter.mp he).1
    exact (edgeGap_pos (hT e.1 he'.1) (hT e.2 he'.2.1) he'.2.2).le

theorem Ypotential_nonneg
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    0 ≤ Ypotential P T := by
  exact Bweight_sub_BP_nonneg T hT P hprime

theorem Zpotential_nonneg
    (T : Finset ℕ) (P : Finset ℕ) (_hprime : ∀ p ∈ P, p.Prime) :
    0 ≤ Zpotential P T := by
  simp only [Zpotential, BP, Bp]
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/- ## Bridge to the valuation-level matching theorem -/

/-- The factorization of the concrete normalizer agrees with the valuation
normalizer used in `Erdos126.Padic`. -/
theorem factorization_normalizer_apply
    {a b p : ℕ} (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) :
    (Normalized.normalizer a b).factorization p =
      Padic.normaliserVal p a b := by
  have hg : a.gcd b ≠ 0 := (Nat.gcd_pos_of_pos_left b ha).ne'
  rw [Normalized.normalizer_eq_if_factorization_two_eq ha hb]
  by_cases heq : a.factorization 2 = b.factorization 2
  · rw [if_pos heq, Nat.factorization_mul (by norm_num) hg,
      Nat.factorization_gcd ha.ne' hb.ne']
    simp only [Finsupp.add_apply, Finsupp.inf_apply]
    rw [Nat.factorization_def a hp, Nat.factorization_def b hp]
    by_cases h2 : p = 2
    · subst p
      have hval : padicValNat 2 a = padicValNat 2 b := by
        simpa [Nat.factorization_def a Nat.prime_two,
          Nat.factorization_def b Nat.prime_two] using heq
      simp [Padic.normaliserVal, Padic.twoCorrection, hval,
        Nat.prime_two.factorization_self]
      omega
    · have hfac : (2 : ℕ).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdvd
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
        exact h2 (Nat.le_antisymm hle hp.two_le)
      simp [Padic.normaliserVal, h2, hfac]
  · rw [if_neg heq]
    simp only [one_mul]
    change (a.gcd b).factorization p = Padic.normaliserVal p a b
    rw [Nat.factorization_gcd ha.ne' hb.ne']
    simp only [Finsupp.inf_apply]
    rw [Nat.factorization_def a hp, Nat.factorization_def b hp]
    by_cases h2 : p = 2
    · subst p
      have hval : padicValNat 2 a ≠ padicValNat 2 b := by
        intro h
        apply heq
        simpa [Nat.factorization_def a Nat.prime_two,
          Nat.factorization_def b Nat.prime_two] using h
      simp [Padic.normaliserVal, Padic.twoCorrection, hval]
    · simp [Padic.normaliserVal, h2]

/-- Concrete normalized-sum valuations equal the direct valuation formula. -/
theorem padicValNat_normalizedSum_eq_normalisedSumVal
    {a b p : ℕ} (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) :
    padicValNat p (Normalized.normalizedSum a b) =
      Padic.normalisedSumVal p a b := by
  rw [← Nat.factorization_def (Normalized.normalizedSum a b) hp]
  rw [Normalized.normalizedSum,
    Nat.factorization_div (Normalized.normalizer_dvd_sum ha hb)]
  simp only [Finsupp.tsub_apply]
  rw [Nat.factorization_def (a + b) hp,
    factorization_normalizer_apply ha hb hp]
  rfl

/-- Concrete normalized-distance valuations equal the direct valuation
formula on positive inputs. -/
theorem padicValNat_normalizedDist_eq_normalisedDiffVal
    {a b p : ℕ} (ha : 0 < a) (hb : 0 < b) (hp : p.Prime) :
    padicValNat p (Normalized.normalizedDist a b) =
      Padic.normalisedDiffVal p a b := by
  rw [← Nat.factorization_def (Normalized.normalizedDist a b) hp]
  rw [Normalized.normalizedDist,
    Nat.factorization_div (Normalized.normalizer_dvd_dist ha hb)]
  simp only [Finsupp.tsub_apply]
  rw [Nat.factorization_def (Nat.dist a b) hp,
    factorization_normalizer_apply ha hb hp]
  rfl

/-- Ordered sum potential expanded using the valuation functions of the
matching theorem. -/
theorem AweightOrdered_eq_sum_normalisedSumVal
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) :
    AweightOrdered T =
      ∑ p ∈ addPrimeSupport T,
        ((∑ e ∈ T.offDiag, Padic.normalisedSumVal p e.1 e.2 : ℕ) : ℝ) *
          Real.log p := by
  rw [AweightOrdered]
  rw [sum_log_normalizedSum_eq_sum_prime_weighted_edge_sum
    T hT T.offDiag (Finset.Subset.rfl)]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_offDiag.mp he
  exact padicValNat_normalizedSum_eq_normalisedSumVal
    (hT e.1 he'.1) (hT e.2 he'.2.1) (prime_of_mem_addPrimeSupport hp)

/-- Ordered restricted distance potential expanded using `normalisedDiffVal`. -/
theorem BPOrdered_eq_sum_normalisedDiffVal
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) :
    BPOrdered (addPrimeSupport T) T =
      ∑ p ∈ addPrimeSupport T,
        ((∑ e ∈ T.offDiag, Padic.normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) *
          Real.log p := by
  simp only [BPOrdered, BpOrdered]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_mul]
  congr 1
  norm_cast
  apply Finset.sum_congr rfl
  intro e he
  have he' := Finset.mem_offDiag.mp he
  exact padicValNat_normalizedDist_eq_normalisedDiffVal
    (hT e.1 he'.1) (hT e.2 he'.2.1) (prime_of_mem_addPrimeSupport hp)

/-- Endpoint cost of an involution in the weighted p-adic theorem. -/
def involutionCost (p : ℕ) {T : Finset ℕ} (τ : T → T) : ℕ :=
  ∑ a ∈ T.attach,
    if τ a ≠ a then Padic.normalisedSumVal p a (τ a) else 0

/-- Exact unlogged slack in the weighted p-adic matching inequality. -/
def pSlack (p : ℕ) (T : Finset ℕ) (τ : T → T) : ℝ :=
  ((∑ e ∈ T.offDiag, Padic.normalisedDiffVal p e.1 e.2 : ℕ) : ℝ) +
    involutionCost p τ -
      (∑ e ∈ T.offDiag, Padic.normalisedSumVal p e.1 e.2 : ℕ)

/-- The logged matching identity is pure finite-sum algebra once the
factorization expansions have been established. -/
theorem logged_involution_identity
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a)
    (τ : ℕ → T → T) :
    AweightOrdered T - BPOrdered (addPrimeSupport T) T +
        (∑ p ∈ addPrimeSupport T, Real.log p * pSlack p T (τ p)) =
      ∑ p ∈ addPrimeSupport T,
        Real.log p * (involutionCost p (τ p) : ℝ) := by
  rw [AweightOrdered_eq_sum_normalisedSumVal T hT,
    BPOrdered_eq_sum_normalisedDiffVal T hT]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [pSlack]
  ring

/-- Simultaneously choose one involution for each support prime.  Every
resulting slack is nonnegative, and the exact logged identity holds. -/
theorem exists_involutions_logged_identity
    (T : Finset ℕ) (hT : ∀ a ∈ T, 0 < a) :
    ∃ τ : ℕ → T → T,
      (∀ p ∈ addPrimeSupport T, Function.Involutive (τ p)) ∧
      (∀ p ∈ addPrimeSupport T, 0 ≤ pSlack p T (τ p)) ∧
      AweightOrdered T - BPOrdered (addPrimeSupport T) T +
          (∑ p ∈ addPrimeSupport T, Real.log p * pSlack p T (τ p)) =
        ∑ p ∈ addPrimeSupport T,
          Real.log p * (involutionCost p (τ p) : ℝ) := by
  classical
  let τ : ℕ → T → T := fun p =>
    if hp : p.Prime then
      Classical.choose (Padic.exists_involution_weighted T p hp hT)
    else id
  refine ⟨τ, ?_, ?_, logged_involution_identity T hT τ⟩
  · intro p hpT
    have hp := prime_of_mem_addPrimeSupport hpT
    dsimp only [τ]
    rw [dif_pos hp]
    exact (Classical.choose_spec
      (Padic.exists_involution_weighted T p hp hT)).1
  · intro p hpT
    have hp := prime_of_mem_addPrimeSupport hpT
    have hspec := Classical.choose_spec
      (Padic.exists_involution_weighted T p hp hT)
    dsimp only [τ]
    rw [dif_pos hp]
    simp only [pSlack]
    exact sub_nonneg.mpr (by exact_mod_cast hspec.2)

end

end Erdos126
