import Mathlib

/-!
Erdos #687 Attempt_F: finite BKQR certificate, independent of external results.
No new axioms or sorry. The CRT step is a named, undischarged premise.
-/
set_option autoImplicit false

namespace MethlibErdos687.AttemptF

def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + (i : ℤ)).natAbs.Coprime n

def SurvivorCount (n y : ℕ) (a : ℤ) : ℕ :=
  ((Finset.range y).filter
    (fun i => (a + (i : ℤ)).natAbs.Coprime n)).card

def FullyCovered (n y : ℕ) : Prop :=
  ∃ a : ℤ, SurvivorCount n y a = 0

theorem survivor_pos_iff (n y : ℕ) (a : ℤ) :
    0 < SurvivorCount n y a ↔
      ∃ i : ℕ, i < y ∧ (a + (i : ℤ)).natAbs.Coprime n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h
    have hf : i ∈ (Finset.range y).filter
        (fun j => (a + (j : ℤ)).natAbs.Coprime n) := hi
    obtain ⟨him, hc⟩ := Finset.mem_filter.mp hf
    exact ⟨i, Finset.mem_range.mp him, hc⟩
  · rintro ⟨i, hi, hc⟩
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hi, hc⟩⟩

theorem survivor_pos_of_jacobsthal
    {k m n y : ℕ} (hJ : IsJacobsthalBound k m)
    (hn : 0 < n) (hcard : n.primeFactors.card ≤ k)
    (hmy : m ≤ y) (a : ℤ) :
    0 < SurvivorCount n y a := by
  obtain ⟨i, hi, hcop⟩ := hJ n hn hcard a
  exact (survivor_pos_iff n y a).2 ⟨i, lt_of_lt_of_le hi hmy, hcop⟩

/-- Two separate Jacobsthal blocks contain two distinct coprime positions. -/
theorem two_blocks (k m n : ℕ) (hJ : IsJacobsthalBound k m)
    (hn : 0 < n) (hcard : n.primeFactors.card ≤ k) (a : ℤ) :
    ∃ i j : ℕ, i < j ∧ j < 2 * m ∧
      (a + (i : ℤ)).natAbs.Coprime n ∧
      (a + (j : ℤ)).natAbs.Coprime n := by
  obtain ⟨i, hi, hci⟩ := hJ n hn hcard a
  obtain ⟨j, hj, hcj⟩ := hJ n hn hcard (a + (m : ℤ))
  refine ⟨i, m + j, ?_, ?_, hci, ?_⟩
  · omega
  · omega
  · simpa only [Nat.cast_add, add_assoc] using hcj

/-- Survivors in residue class r modulo q, after the P-sieve. -/
def ResidueCount (P q y : ℕ) (a : ℤ) (r : Fin q) : ℕ :=
  ((Finset.range y).filter
    (fun i => (a + (i : ℤ)).natAbs.Coprime P ∧ i % q = r.val)).card

/-- Ordered cross-class pairs: nonnegative BKQR dispersion. -/
def Delta (P q y : ℕ) (a : ℤ) : ℕ :=
  ∑ r : Fin q, ∑ u : Fin q,
    if r = u then 0
    else ResidueCount P q y a r * ResidueCount P q y a u

def U (P q y : ℕ) : ℕ :=
  ∑ t : Fin P, Delta P q y (t.val : ℤ)

def B (P q y : ℕ) : ℕ :=
  ∑ t : Fin P, (Delta P q y (t.val : ℤ)) ^ 2

/-- Finite Cauchy certificate with no number-theoretic assumptions. -/
theorem moment_strict_forces_all_positive
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (h : (∑ i ∈ s, f i) ^ 2 >
      (s.card - 1) * ∑ i ∈ s, f i ^ 2) :
    ∀ i ∈ s, 0 < f i := by
  intro i hi
  by_contra hnot
  have hzero : f i = 0 := by omega
  have hs : (∑ j ∈ s.erase i, f j) = ∑ j ∈ s, f j := by
    calc
      (∑ j ∈ s.erase i, f j) =
          (∑ j ∈ s.erase i, f j) + f i := by simp [hzero]
      _ = ∑ j ∈ s, f j := Finset.sum_erase_add s f hi
  have hs2 : (∑ j ∈ s.erase i, f j ^ 2) =
      ∑ j ∈ s, f j ^ 2 := by
    calc
      (∑ j ∈ s.erase i, f j ^ 2) =
          (∑ j ∈ s.erase i, f j ^ 2) + f i ^ 2 := by simp [hzero]
      _ = ∑ j ∈ s, f j ^ 2 :=
        Finset.sum_erase_add s (fun j => f j ^ 2) hi
  have hc : (s.erase i).card = s.card - 1 :=
    Finset.card_erase_of_mem hi
  have hcs : (∑ j ∈ s.erase i, f j) ^ 2 ≤
      (s.erase i).card * ∑ j ∈ s.erase i, f j ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hs, hs2, hc] at hcs
  exact (not_lt_of_ge hcs) h

theorem moment_certificate_sound (P q y : ℕ)
    (hCert : (P - 1) * B P q y < (U P q y) ^ 2) :
    ∀ t : Fin P, 0 < Delta P q y (t.val : ℤ) := by
  have hCriterion :
      (∑ t : Fin P, Delta P q y (t.val : ℤ)) ^ 2 >
        ((Finset.univ : Finset (Fin P)).card - 1) *
        ∑ t : Fin P, (Delta P q y (t.val : ℤ)) ^ 2 := by
    simpa [U, B] using hCert
  have hAll := moment_strict_forces_all_positive
    (s := (Finset.univ : Finset (Fin P)))
    (f := fun t : Fin P => Delta P q y (t.val : ℤ)) hCriterion
  intro t
  exact hAll t (Finset.mem_univ t)

def checkDelta (P q y : ℕ) : Bool :=
  decide (∀ t : Fin P, 0 < Delta P q y (t.val : ℤ))

theorem checkDelta_iff (P q y : ℕ) :
    checkDelta P q y = true ↔
      ∀ t : Fin P, 0 < Delta P q y (t.val : ℤ) := by
  simp [checkDelta]

theorem moment_certificate_accepted (P q y : ℕ)
    (hCert : (P - 1) * B P q y < (U P q y) ^ 2) :
    checkDelta P q y = true :=
  (checkDelta_iff P q y).2
    (moment_certificate_sound P q y hCert)

/-- Named OPEN CRT transfer. It is a hypothesis, not a theorem/axiom. -/
def CRTDispersionBridge (P q y : ℕ) : Prop :=
  (∀ t : Fin P, 0 < Delta P q y (t.val : ℤ)) ↔
    ¬ FullyCovered (P * q) y

theorem certificate_excludes_cover {P q y : ℕ}
    (hCRT : CRTDispersionBridge P q y)
    (hCert : (P - 1) * B P q y < (U P q y) ^ 2) :
    ¬ FullyCovered (P * q) y :=
  hCRT.mp (moment_certificate_sound P q y hCert)

end MethlibErdos687.AttemptF
