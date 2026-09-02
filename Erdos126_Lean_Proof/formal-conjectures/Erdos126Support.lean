import FormalConjectures.ErdosProblems.«126»

namespace Erdos126

/-- The primes which divide an off-diagonal pairwise sum from `A`.

We use only the orientation `a < b`.  Thus an unordered pair contributes once,
even though the product in `IsMaximalAddFactorsCard` ranges over both `(a, b)`
and `(b, a)`. -/
def addPrimeSupport (A : Finset ℕ) : Finset ℕ :=
  (A.offDiag.filter fun ab => ab.1 < ab.2).biUnion
    fun ab => (ab.1 + ab.2).primeFactors

private theorem primeFactors_prod_eq_biUnion
    {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℕ)
    (hg : ∀ x ∈ s, g x ≠ 0) :
    (∏ x ∈ s, g x).primeFactors = s.biUnion fun x => (g x).primeFactors := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have hx : g x ≠ 0 := hg x (by simp)
      have hs : (∏ y ∈ s, g y) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr fun y hy => hg y (by simp [hy])
      rw [Finset.prod_insert hxs, Nat.primeFactors_mul hx hs, ih]
      · simp
      · intro y hy
        exact hg y (by simp [hy])

private theorem offDiagPrimeSupport_eq_strict (A : Finset ℕ) :
    A.offDiag.biUnion (fun ab => (ab.1 + ab.2).primeFactors) =
      (A.offDiag.filter fun ab => ab.1 < ab.2).biUnion
        fun ab => (ab.1 + ab.2).primeFactors := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, hp⟩
    rcases lt_trichotomy a b with hab' | hab' | hab'
    · exact ⟨(a, b), ⟨⟨ha, hb, hab⟩, hab'⟩, hp⟩
    · exact (hab hab').elim
    · refine ⟨(b, a), ⟨⟨hb, ha, hab.symm⟩, hab'⟩, ?_⟩
      simpa [Nat.add_comm] using hp
  · rintro ⟨ab, ⟨hab, _⟩, hp⟩
    exact ⟨ab, hab, hp⟩

/-- The semantic support of the pairwise sums is the prime support of the
ordered off-diagonal product used in the official statement. -/
theorem addPrimeSupport_eq_primeFactors_prod (A : Finset ℕ) :
    addPrimeSupport A =
      (∏ ab ∈ A.offDiag, (ab.1 + ab.2)).primeFactors := by
  classical
  rw [addPrimeSupport, ← offDiagPrimeSupport_eq_strict]
  symm
  apply primeFactors_prod_eq_biUnion
  intro ab hab
  simp only [Finset.mem_offDiag] at hab
  intro hzero
  obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp hzero
  exact hab.2.2 (ha.trans hb.symm)

/-- Cardinality form, in exactly the notation used by
`IsMaximalAddFactorsCard`. -/
theorem addPrimeSupport_card_eq_offDiagProduct (A : Finset ℕ) :
    (addPrimeSupport A).card =
      (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card := by
  rw [addPrimeSupport_eq_primeFactors_prod]

/-- Any lower bound proved uniformly for all `n`-element sets is at most the
maximal lower bound from the official formulation. -/
theorem le_maximalAddFactorsCard
    (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) {n m : ℕ}
    (h : ∀ (A : Finset ℕ), A.card = n → m ≤ (addPrimeSupport A).card) :
    m ≤ f n := by
  apply (hf n).2
  change ∀ (A : Finset ℕ), A.card = n →
    m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card
  intro A hA
  rw [← addPrimeSupport_card_eq_offDiagProduct]
  exact h A hA

/-- Function-valued version of `le_maximalAddFactorsCard`. -/
theorem lowerBound_le_maximalAddFactorsCard
    (f g : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f)
    (hg : ∀ n (A : Finset ℕ), A.card = n →
      g n ≤ (addPrimeSupport A).card) :
    ∀ n, g n ≤ f n := by
  intro n
  exact le_maximalAddFactorsCard f hf (hg n)

end Erdos126
