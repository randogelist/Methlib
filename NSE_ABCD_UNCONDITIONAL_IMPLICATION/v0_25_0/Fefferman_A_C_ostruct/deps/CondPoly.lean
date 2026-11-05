import CondJets

noncomputable section

namespace CondPoly

/-- Partial exponential sums occurring in the Taylor expansion of
    exp(-s) / (1+s). -/
def expPartial (j : ℕ) : ℝ :=
  (Finset.range (j + 1)).sum fun k => (k.factorial : ℝ)⁻¹

theorem expPartial_succ (j : ℕ) :
    expPartial (j + 1) = expPartial j + ((j + 1).factorial : ℝ)⁻¹ := by
  exact Finset.sum_range_succ (fun k : ℕ => (k.factorial : ℝ)⁻¹) (j + 1)

def radialCoeff (j : ℕ) : ℝ := (-1 : ℝ) ^ j * expPartial j

/-- Multiplying the sequence by the polynomial 1+s recovers the
    scalar exponential coefficients. -/
theorem radialCoeff_zero : radialCoeff 0 = 1 := by
  norm_num [radialCoeff, expPartial]

theorem radialCoeff_denominator (j : ℕ) :
    radialCoeff (j + 1) + radialCoeff j =
      (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)⁻¹ := by
  simp only [radialCoeff, expPartial_succ, pow_succ] <;> ring

theorem radialCoeff_unique (b : ℕ → ℝ) (hzero : b 0 = 1)
    (hcoeff : ∀ j : ℕ, b (j + 1) + b j =
      (-1 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)⁻¹) :
    b = radialCoeff := by
  funext j
  induction j with
  | zero => exact hzero.trans radialCoeff_zero.symm
  | succ j ih =>
    linarith only [hcoeff j, radialCoeff_denominator j, ih]

/-- For s=|x|² in dimension three, the formal radial Laplacian has
    coefficient (2k+2)(2k+3) at the shift from s^(k+1) to s^k. -/
def radialDelta (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3) * a (k + 1)

def radialDeltaIter : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, a => a
  | n + 1, a => radialDeltaIter n (radialDelta a)

def radialWeight : ℕ → ℝ
  | 0 => 1
  | n + 1 => radialWeight n * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)

theorem radialDeltaIter_at_zero (n : ℕ) (a : ℕ → ℝ) :
    radialDeltaIter n a 0 = radialWeight n * a n := by
  induction n generalizing a with
  | zero => simp [radialDeltaIter, radialWeight]
  | succ n ih =>
    rw [radialDeltaIter, ih, radialWeight, radialDelta] <;> ring

theorem radialWeight_eq_factorial (j : ℕ) :
    radialWeight j = ((2 * j + 1).factorial : ℝ) := by
  induction j with
  | zero => norm_num [radialWeight]
  | succ j ih =>
    have h : 2 * (j + 1) + 1 = (2 * j + 1 + 1) + 1 := by omega
    rw [radialWeight, ih, h, Nat.factorial_succ (2 * j + 1 + 1),
      Nat.factorial_succ (2 * j + 1)]
    push_cast <;> ring

/-- The algebraic jet with the solenoidal projection factor 2/3.
    Identification with a spatial derivative is a separate premise. -/
def radialJet (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) * radialDeltaIter (n + 1) radialCoeff 0

theorem radialJet_signed (n : ℕ) :
    radialJet n = (-1 : ℝ) ^ (n + 1) * CondFeffA.radialLinearMagnitude n := by
  have h : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  rw [radialJet, radialDeltaIter_at_zero, radialWeight_eq_factorial, h]
  simp only [radialCoeff, expPartial, CondFeffA.radialLinearMagnitude, one_div] <;> ring

theorem abs_radialJet (n : ℕ) :
    |radialJet n| = CondFeffA.radialLinearMagnitude n := by
  have hmag : 0 ≤ CondFeffA.radialLinearMagnitude n :=
    (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ)).trans
      (CondFeffA.radial_linear_magnitude_lower n)
  simp [radialJet_signed, abs_mul, abs_pow, abs_of_nonneg hmag]

theorem radialJet_has_no_factorial_bound :
    ¬ CondFeffA.FactorialJetBound radialJet :=
  CondFeffA.exact_radial_coefficients_exclude_factorial_bound abs_radialJet

end CondPoly

end

#print axioms CondPoly.radialCoeff_denominator
#print axioms CondPoly.radialCoeff_unique
#print axioms CondPoly.radialDeltaIter_at_zero
#print axioms CondPoly.radialWeight_eq_factorial
#print axioms CondPoly.radialJet_signed
#print axioms CondPoly.abs_radialJet
#print axioms CondPoly.radialJet_has_no_factorial_bound
