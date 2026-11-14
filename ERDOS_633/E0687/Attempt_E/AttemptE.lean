import Mathlib

/-!
Erdos #687 Attempt_E. The exact finite moment certificate and a
conditional implication from the published quadratic Jacobsthal theorem.
The external endpoint is discharged in ExternalRoot.lean.
-/

namespace Erdos687AttemptE

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

def JacobsthalQuadratic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
    ∃ m : ℕ, IsJacobsthalBound k m ∧ (m : ℝ) ≤ C * (k : ℝ) ^ 2

def survivorCount (n H : ℕ) (a : ℤ) : ℕ :=
  ((Finset.range H).filter
    (fun i : ℕ => (a + (i : ℤ)).natAbs.Coprime n)).card

def coveredCount (n H : ℕ) : ℕ :=
  ((Finset.range n).filter
    (fun t : ℕ => survivorCount n H (t : ℤ) = 0)).card

def CoveredBlock (n H : ℕ) : Prop :=
  ∃ a : ℤ, ∀ i : ℕ, i < H → ¬ (a + (i : ℤ)).natAbs.Coprime n

def exactDetector (H u : ℕ) : ℚ :=
  ∏ j ∈ Finset.range H, (1 - (u : ℚ) / ((j + 1 : ℕ) : ℚ))

def momentCertificate (n H : ℕ) : ℚ :=
  ∑ t ∈ Finset.range n,
    (exactDetector H (survivorCount n H (t : ℤ))) ^ 2

def finiteCheck (n H : ℕ) : Bool := decide (coveredCount n H = 0)

theorem exactDetector_zero (H : ℕ) : exactDetector H 0 = 1 := by
  simp [exactDetector]

theorem exactDetector_pos_zero {H u : ℕ} (hu : 0 < u) (hule : u ≤ H) :
    exactDetector H u = 0 := by
  unfold exactDetector
  have hj : u - 1 ∈ Finset.range H := Finset.mem_range.mpr (by omega)
  have hfactor :
      (1 - (u : ℚ) / (((u - 1) + 1 : ℕ) : ℚ)) = 0 := by
    have hs : u - 1 + 1 = u := by omega
    rw [hs]
    have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
    simp [huq]
  exact Finset.prod_eq_zero hj hfactor

theorem survivorCount_le (n H : ℕ) (a : ℤ) : survivorCount n H a ≤ H := by
  unfold survivorCount
  exact (Finset.card_filter_le (Finset.range H)
    (fun i : ℕ => (a + (i : ℤ)).natAbs.Coprime n)).trans (by simp)

theorem exactDetector_sq_ite (H u : ℕ) (hule : u ≤ H) :
    (exactDetector H u) ^ 2 = if u = 0 then (1 : ℚ) else 0 := by
  by_cases hzero : u = 0
  · subst u
    simp [exactDetector]
  · have hu : 0 < u := Nat.pos_of_ne_zero hzero
    rw [exactDetector_pos_zero hu hule]
    simp [hzero]

theorem momentCertificate_eq_coveredCount (n H : ℕ) :
    momentCertificate n H = (coveredCount n H : ℚ) := by
  classical
  calc
    momentCertificate n H =
        ∑ t ∈ Finset.range n,
          (if survivorCount n H (t : ℤ) = 0 then (1 : ℚ) else 0) := by
      unfold momentCertificate
      apply Finset.sum_congr rfl
      intro t _ht
      exact exactDetector_sq_ite H (survivorCount n H (t : ℤ))
        (survivorCount_le n H (t : ℤ))
    _ = (coveredCount n H : ℚ) := by
      simp [coveredCount, Finset.card_filter]

theorem momentCertificate_nonneg (n H : ℕ) :
    (0 : ℚ) ≤ momentCertificate n H := by
  unfold momentCertificate
  apply Finset.sum_nonneg
  intro t ht
  positivity

theorem finiteCheck_sound {n H : ℕ} (h : finiteCheck n H = true) :
    coveredCount n H = 0 := by
  simpa [finiteCheck] using h

theorem finiteCheck_of_zero {n H : ℕ} (h : coveredCount n H = 0) :
    finiteCheck n H = true := by
  simp [finiteCheck, h]

def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

def primorial (x : ℕ) : ℕ :=
  ∏ p ∈ primesUpTo x, p

def primeCount (x : ℕ) : ℕ := (primesUpTo x).card

theorem prime_of_mem_primesUpTo {x p : ℕ} (hp : p ∈ primesUpTo x) :
    Nat.Prime p := (Finset.mem_filter.mp hp).2

theorem primorial_pos (x : ℕ) : 0 < primorial x := by
  unfold primorial
  apply Finset.prod_pos
  intro p hp
  exact (prime_of_mem_primesUpTo hp).pos

theorem primorial_primeFactors (x : ℕ) :
    (primorial x).primeFactors = primesUpTo x := by
  unfold primorial
  exact Nat.primeFactors_prod (fun p hp => prime_of_mem_primesUpTo hp)

theorem primeCount_pos {x : ℕ} (hx : 2 ≤ x) : 0 < primeCount x := by
  have htwo : 2 ∈ primesUpTo x := by
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · exact Nat.prime_two
  exact Finset.card_pos.mpr ⟨2, htwo⟩

theorem survivorCount_pos_of_bound {k m n H : ℕ}
    (hb : IsJacobsthalBound k m)
    (hn : 0 < n) (hfac : n.primeFactors.card ≤ k)
    (hmH : m ≤ H) (a : ℤ) : 0 < survivorCount n H a := by
  obtain ⟨i, hi, hcop⟩ := hb n hn hfac a
  unfold survivorCount
  apply Finset.card_pos.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le hi hmH), ?_⟩⟩
  simpa using hcop

theorem coveredCount_zero_of_bound {k m n H : ℕ}
    (hb : IsJacobsthalBound k m)
    (hn : 0 < n) (hfac : n.primeFactors.card ≤ k)
    (hmH : m ≤ H) : coveredCount n H = 0 := by
  have hNone : ∀ t : ℕ, ¬ survivorCount n H (t : ℤ) = 0 := by
    intro t ht
    have hp := survivorCount_pos_of_bound hb hn hfac hmH (t : ℤ)
    omega
  simp [coveredCount, hNone]

theorem noCoveredBlock_of_bound {k m n H : ℕ}
    (hb : IsJacobsthalBound k m)
    (hn : 0 < n) (hfac : n.primeFactors.card ≤ k)
    (hmH : m ≤ H) : ¬ CoveredBlock n H := by
  intro h
  obtain ⟨a, ha⟩ := h
  obtain ⟨i, hi, hcop⟩ := hb n hn hfac a
  exact (ha i (lt_of_lt_of_le hi hmH)) hcop

theorem quadratic_finite_certificate (hquad : JacobsthalQuadratic) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 0 < k → ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
        ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
          ∀ H : ℕ, m ≤ H →
            ¬ CoveredBlock n H ∧
            coveredCount n H = 0 ∧
            momentCertificate n H = 0 := by
  obtain ⟨C, hC, hBound⟩ := hquad
  refine ⟨C, hC, ?_⟩
  intro k hk n hn hfac
  obtain ⟨m, hb, hm⟩ := hBound k hk
  refine ⟨m, hm, ?_⟩
  intro H hmH
  have hz : coveredCount n H = 0 :=
    coveredCount_zero_of_bound hb hn hfac hmH
  refine ⟨noCoveredBlock_of_bound hb hn hfac hmH, hz, ?_⟩
  simpa [momentCertificate_eq_coveredCount, hz]

theorem quadratic_all_moduli (hquad : JacobsthalQuadratic) :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 0 < n →
        ∃ m : ℕ,
          (m : ℝ) ≤ C * ((n.primeFactors.card + 1 : ℕ) : ℝ) ^ 2 ∧
          ∀ H : ℕ, m ≤ H →
            ¬ CoveredBlock n H ∧
            coveredCount n H = 0 ∧
            momentCertificate n H = 0 := by
  obtain ⟨C, hC, hBridge⟩ := quadratic_finite_certificate hquad
  refine ⟨C, hC, ?_⟩
  intro n hn
  exact hBridge (n.primeFactors.card + 1) (by omega) n hn (by omega)

theorem quadratic_prime_cutoff (hquad : JacobsthalQuadratic) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℕ, 2 ≤ x →
        ∃ m : ℕ, (m : ℝ) ≤ C * (primeCount x : ℝ) ^ 2 ∧
          ∀ H : ℕ, m ≤ H →
            ¬ CoveredBlock (primorial x) H ∧
            coveredCount (primorial x) H = 0 ∧
            momentCertificate (primorial x) H = 0 ∧
            finiteCheck (primorial x) H = true := by
  obtain ⟨C, hC, hBridge⟩ := quadratic_finite_certificate hquad
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hPrimeCount : 0 < primeCount x := primeCount_pos hx
  have hFactors : (primorial x).primeFactors.card ≤ primeCount x := by
    simp [primorial_primeFactors, primeCount]
  obtain ⟨m, hm, hRest⟩ :=
    hBridge (primeCount x) hPrimeCount (primorial x)
      (primorial_pos x) hFactors
  refine ⟨m, hm, ?_⟩
  intro H hmH
  obtain ⟨hNoCover, hZ, hW⟩ := hRest H hmH
  exact ⟨hNoCover, hZ, hW, finiteCheck_of_zero hZ⟩

#print axioms Erdos687AttemptE.momentCertificate_eq_coveredCount
#print axioms Erdos687AttemptE.quadratic_finite_certificate
#print axioms Erdos687AttemptE.quadratic_all_moduli
#print axioms Erdos687AttemptE.quadratic_prime_cutoff

end Erdos687AttemptE
