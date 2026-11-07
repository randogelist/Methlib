import Mathlib

/-!
Erdos #687, Attempt_C: exact finite rational survivor certificate.
The global x^(1+o(1)) frontier is NOT proved here.
-/
namespace Erdos687AttemptC

open scoped BigOperators

def survivors (P y b : ℕ) : ℕ :=
  ((Finset.Icc 1 y).filter (fun n => Nat.Coprime (b + n) P)).card

theorem survivors_le (P y b : ℕ) : survivors P y b ≤ y := by
  unfold survivors
  calc
    ((Finset.Icc 1 y).filter (fun n => Nat.Coprime (b + n) P)).card
        ≤ (Finset.Icc 1 y).card := Finset.card_filter_le _ _
    _ = y := by simp [Nat.card_Icc]

def EveryShiftSurvives (P y : ℕ) : Prop :=
  ∀ b : ℕ, b < P → 0 < survivors P y b

def spike (y s : ℕ) : ℚ :=
  ∏ j ∈ Finset.Icc 1 y, ((1 : ℚ) - (s : ℚ) / (j : ℚ))

theorem spike_at_zero (y : ℕ) : spike y 0 = 1 := by
  simp [spike]

theorem spike_at_positive {y s : ℕ} (hs : 0 < s) (hsy : s ≤ y) :
    spike y s = 0 := by
  unfold spike
  apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hs, hsy⟩)
  have hn : (s : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  simp [hn]

def certificateMass (P y : ℕ) (q : ℕ → ℚ) : ℚ :=
  ∑ b ∈ Finset.range P, (q (survivors P y b)) ^ 2

/-- !! Exact finite rational certificate: all shifts survive iff the mass is below one. -/
theorem spike_certificate_iff (P y : ℕ) :
    certificateMass P y (spike y) < 1 ↔ EveryShiftSurvives P y := by
  constructor
  · intro h b hb
    by_contra hn
    have hz : survivors P y b = 0 := by omega
    have hsingle :
        (spike y (survivors P y b)) ^ 2 ≤ certificateMass P y (spike y) := by
      unfold certificateMass
      exact Finset.single_le_sum
        (fun t _ => sq_nonneg (spike y (survivors P y t)))
        (Finset.mem_range.mpr hb)
    have hbad : (1 : ℚ) ≤ certificateMass P y (spike y) := by
      simpa [hz, spike_at_zero] using hsingle
    exact (not_lt_of_ge hbad) h
  · intro h
    have heq : certificateMass P y (spike y) = 0 := by
      unfold certificateMass
      apply Finset.sum_eq_zero
      intro b hb
      have hpos : 0 < survivors P y b := h b (Finset.mem_range.mp hb)
      have hle : survivors P y b ≤ y := survivors_le P y b
      rw [spike_at_positive hpos hle]
      norm_num
    rw [heq]
    norm_num

/-- Reproduces the signed-residue covering statement from the external glue. -/
def Covers (x y : ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ y →
    ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ (n : ℤ) ≡ a p [ZMOD p]

def ExternalPartialBound : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in Filter.atTop,
    ∀ y : ℕ, ∀ a : ℕ → ℤ, Covers x y a →
      (y : ℝ) ≤ ε * (x : ℝ) ^ 2

theorem external_partial_plus_certificate (h : ExternalPartialBound) :
    ExternalPartialBound ∧
      (∀ x y : ℕ,
        certificateMass (primorial x) y (spike y) < 1 ↔
          EveryShiftSurvives (primorial x) y) := by
  exact ⟨h, fun x y => spike_certificate_iff (primorial x) y⟩

/-- Open interface: CRT conversion of signed classes to a primorial shift. -/
def CRTSemanticBridge : Prop :=
  ∀ x y : ℕ,
    (∃ a : ℕ → ℤ, Covers x y a) ↔
      ¬ EveryShiftSurvives (primorial x) y

theorem certificate_excludes_covers
    (hCRT : CRTSemanticBridge) (x y : ℕ)
    (hcert : certificateMass (primorial x) y (spike y) < 1) :
    ¬ ∃ a : ℕ → ℤ, Covers x y a := by
  intro hcov
  have hbad := (hCRT x y).mp hcov
  exact hbad ((spike_certificate_iff (primorial x) y).mp hcert)

/-- ! Any rational separator with uniformly small values admits the same exact test. -/
theorem small_rational_certificate_iff
    (P y : ℕ) (q : ℕ → ℚ)
    (hq0 : q 0 = 1)
    (hsmall : ∀ s : ℕ, 0 < s → s ≤ y →
      (q s) ^ 2 ≤ (1 : ℚ) / ((P : ℚ) + 1)) :
    certificateMass P y q < 1 ↔ EveryShiftSurvives P y := by
  constructor
  · intro h b hb
    by_contra hn
    have hz : survivors P y b = 0 := by omega
    have hsingle : (q (survivors P y b)) ^ 2 ≤ certificateMass P y q := by
      unfold certificateMass
      exact Finset.single_le_sum
        (fun t _ => sq_nonneg (q (survivors P y t)))
        (Finset.mem_range.mpr hb)
    have hbad : (1 : ℚ) ≤ certificateMass P y q := by
      simpa [hz, hq0] using hsingle
    exact (not_lt_of_ge hbad) h
  · intro h
    have hbound : certificateMass P y q ≤ (P : ℚ) / ((P : ℚ) + 1) := by
      unfold certificateMass
      calc
        (∑ b ∈ Finset.range P, (q (survivors P y b)) ^ 2)
            ≤ ∑ b ∈ Finset.range P, (1 : ℚ) / ((P : ℚ) + 1) := by
              apply Finset.sum_le_sum
              intro b hb
              exact hsmall _ (h b (Finset.mem_range.mp hb)) (survivors_le P y b)
        _ = (P : ℚ) / ((P : ℚ) + 1) := by
              simp [div_eq_mul_inv, mul_comm]
    have hlt : (P : ℚ) / ((P : ℚ) + 1) < 1 := by
      have hd : (0 : ℚ) < (P : ℚ) + 1 := by positivity
      apply (div_lt_iff₀ hd).2
      linarith
    exact lt_of_le_of_lt hbound hlt

#print axioms Erdos687AttemptC.spike_certificate_iff
#print axioms Erdos687AttemptC.external_partial_plus_certificate
#print axioms Erdos687AttemptC.certificate_excludes_covers
#print axioms Erdos687AttemptC.small_rational_certificate_iff

end Erdos687AttemptC
