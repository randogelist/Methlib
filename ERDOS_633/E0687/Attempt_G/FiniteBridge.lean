import Mathlib

/-!
Erdos #687 / Attempt_G.
Finite Gram reduction (unconditional). No local Lean execution.
The external quantitative theorem is supplied in ExternalRoot.lean.
-/

namespace Erdos687AttemptG

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalQuadratic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧
      (m : ℝ) ≤ C * (k : ℝ) ^ 2

noncomputable def survivorCount (n m : ℕ) (a : ℤ) : ℕ := by
  classical
  exact ((Finset.range m).filter
    (fun i : ℕ => (a + i).natAbs.Coprime n)).card

noncomputable def gramForm (A : Finset ℤ) (n m : ℕ)
    (f : ℕ → ℤ) : ℤ :=
  A.sum (fun a => ((survivorCount n m a : ℤ) - 1) *
    (f (survivorCount n m a)) ^ 2)

def zeroProbe (t : ℕ) : ℤ :=
  if t = 0 then 1 else 0

private theorem zeroProbe_term (t : ℕ) :
    ((t : ℤ) - 1) * (zeroProbe t) ^ 2 =
      (if t = 0 then (-1 : ℤ) else 0) := by
  by_cases ht : t = 0
  · subst t
    simp [zeroProbe]
  · simp [zeroProbe, ht]

private theorem zeroProbe_nonpos (t : ℕ) :
    ((t : ℤ) - 1) * (zeroProbe t) ^ 2 ≤ 0 := by
  rw [zeroProbe_term]
  split_ifs <;> norm_num

/-- Every finite translated-block Gram form is nonnegative exactly when
no tested shift has zero coprime survivors. -/
theorem gram_psd_iff_survivors_positive (A : Finset ℤ) (n m : ℕ) :
    (∀ f : ℕ → ℤ, 0 ≤ gramForm A n m f) ↔
      ∀ a ∈ A, 0 < survivorCount n m a := by
  classical
  constructor
  · intro hpsd a ha
    by_contra hnot
    have hzero : survivorCount n m a = 0 := by omega
    let term : ℤ → ℤ := fun b =>
      ((survivorCount n m b : ℤ) - 1) *
        (zeroProbe (survivorCount n m b)) ^ 2
    have hrest : (A.erase a).sum term ≤ 0 := by
      apply Finset.sum_nonpos
      intro b hb
      exact zeroProbe_nonpos (survivorCount n m b)
    have hvalue : term a = -1 := by
      change ((survivorCount n m a : ℤ) - 1) *
        (zeroProbe (survivorCount n m a)) ^ 2 = -1
      rw [zeroProbe_term]
      simp [hzero]
    have hsplit : gramForm A n m zeroProbe =
        (A.erase a).sum term + term a := by
      simpa [gramForm, term] using
        (Finset.sum_erase_add A term ha).symm
    have hnonneg : 0 ≤ gramForm A n m zeroProbe := hpsd zeroProbe
    rw [hsplit, hvalue] at hnonneg
    omega
  · intro hpositive f
    change 0 ≤ A.sum (fun a => ((survivorCount n m a : ℤ) - 1) *
      (f (survivorCount n m a)) ^ 2)
    apply Finset.sum_nonneg
    intro a ha
    have hpos : 0 < survivorCount n m a := hpositive a ha
    have hfactor : (0 : ℤ) ≤ (survivorCount n m a : ℤ) - 1 := by omega
    exact mul_nonneg hfactor (sq_nonneg _)

theorem survivorCount_pos_of_jacobsthal {k m n : ℕ}
    (hJ : IsJacobsthalBound k m) (hn : 0 < n)
    (hcard : n.primeFactors.card ≤ k) (a : ℤ) :
    0 < survivorCount n m a := by
  classical
  obtain ⟨i, him, hcoprime⟩ := hJ n hn hcard a
  unfold survivorCount
  apply Finset.card_pos.mpr
  exact ⟨i, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr him, hcoprime⟩⟩

def coverableByPrimeFactors (n m : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℕ, i < m →
    ¬ (a + i).natAbs.Coprime n

theorem no_cover_of_jacobsthal {k m n : ℕ}
    (hJ : IsJacobsthalBound k m) (hn : 0 < n)
    (hcard : n.primeFactors.card ≤ k) :
    ¬ coverableByPrimeFactors n m := by
  rintro ⟨a, ha⟩
  obtain ⟨i, him, hcoprime⟩ := hJ n hn hcard a
  exact ha i him hcoprime

/-- Exact quantitative adapter, conditional on the *named*
JacobsthalQuadratic premise. -/
theorem jacobsthal_quadratic_to_prime_gram
    (h : JacobsthalQuadratic) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
        ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
          (¬ coverableByPrimeFactors n m) ∧
          (∀ a : ℤ, 0 < survivorCount n m a) ∧
          (∀ A : Finset ℤ, ∀ f : ℕ → ℤ,
            0 ≤ gramForm A n m f) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hmJacobsthal, hmBound⟩ := hbound k hk
  refine ⟨m, hmBound, ?_⟩
  intro n hn hcard
  constructor
  · exact no_cover_of_jacobsthal hmJacobsthal hn hcard
  constructor
  · intro a
    exact survivorCount_pos_of_jacobsthal hmJacobsthal hn hcard a
  · intro A f
    exact (gram_psd_iff_survivors_positive A n m).2
      (fun a _ => survivorCount_pos_of_jacobsthal
        hmJacobsthal hn hcard a) f

end Erdos687AttemptG

#print axioms Erdos687AttemptG.gram_psd_iff_survivors_positive
#print axioms Erdos687AttemptG.jacobsthal_quadratic_to_prime_gram
