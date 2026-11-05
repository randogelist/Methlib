import Mathlib

namespace CondFeffA

/-- The factorial quotient for a rank j from d+1 ordered nodes is bounded
by a binomial coefficient and hence by 2^d. -/
theorem factorial_le_two_pow_mul_split (d j : ℕ) (hj : j ≤ d) :
    d.factorial ≤ 2^d * j.factorial * (d - j).factorial := by
  calc
    d.factorial = d.choose j * j.factorial * (d - j).factorial :=
      (Nat.choose_mul_factorial_mul_factorial hj).symm
    _ ≤ 2 ^ d * j.factorial * (d - j).factorial := by
      gcongr <;> exact Nat.choose_le_two_pow d j

private theorem real_succ_le_two_pow (d : ℕ) : (d : ℝ) + 1 ≤ 2 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [Nat.cast_succ, pow_succ]
    have hnonneg : 0 ≤ (d : ℝ) := by positivity
    linarith

/-- Removing the spacing loss. The exponential power series at d+2 bounds
(d+2)^d/d!, without an asymptotic Stirling estimate or limit argument. -/
theorem spacing_factorial_estimate (d : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) + 2)^d / (d.factorial : ℝ) ≤ (Real.exp 3)^d := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  calc
    ((d : ℝ) + 2)^d / (d.factorial : ℝ) ≤ Real.exp ((d : ℝ) + 2) :=
      Real.pow_div_factorial_le_exp _ (by positivity) d
    _ ≤ Real.exp ((d : ℝ) * 3) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_nat_mul 3 d

/-- Uniform geometric estimate with d+1 nodes and the spacing
mu/(4(d+2)). R bounds all node magnitudes, and mu is the level-set length. -/
theorem uniform_lagrange_weight_envelope (μ R : ℝ) (hμ : 0 < μ) (hR : 0 ≤ R) :
    ∃ B : ℕ, ∀ d : ℕ, 1 ≤ d →
      (((d : ℝ) + 1) * d * R ^ d * 2 ^ d) *
          (4 * ((d : ℝ) + 2) / μ) ^ d / (d.factorial : ℝ) ≤ (B : ℝ)^d := by
  obtain ⟨B, hB⟩ := exists_nat_gt (2 * 2 * R * 2 * (4 / μ) * Real.exp 3)
  refine ⟨B, ?_⟩
  intro d hd
  have hd1 := real_succ_le_two_pow d
  have hd0 : (d : ℝ) ≤ 2 ^ d := by linarith
  have he := spacing_factorial_estimate d hd
  have hbase : 0 ≤ 2 * 2 * R * 2 * (4 / μ) * Real.exp 3 := by positivity
  calc
    (((d : ℝ) + 1) * d * R ^ d * 2 ^ d) *
          (4 * ((d : ℝ) + 2) / μ) ^ d / (d.factorial : ℝ) =
        (((d : ℝ) + 1) * d * R ^ d * 2 ^ d * (4 / μ)^d) *
          (((d : ℝ) + 2)^d / (d.factorial : ℝ)) := by
            rw [show 4 * ((d : ℝ) + 2) / μ = (4/μ) * ((d : ℝ) + 2) by ring, mul_pow]
            ring
    _ ≤ (2^d * 2^d * R^d * 2^d * (4/μ)^d) * (Real.exp 3)^d := by
        gcongr
    _ = (2 * 2 * R * 2 * (4 / μ) * Real.exp 3)^d := by simp only [mul_pow]
    _ ≤ (B : ℝ)^d := pow_le_pow_left₀ hbase hB.le d

/-- Common geometric bound for the sum of the reciprocal denominator products
on d+1 nodes, once the factorial lower bounds are available. -/
theorem reciprocal_weight_envelope {μ : ℝ} (hμ : 0 < μ) :
    ∃ B : ℕ, ∀ d : ℕ, 1 ≤ d →
      ((d : ℝ) + 1) * (2 : ℝ)^d * (4 * ((d : ℝ) + 2) / μ)^d /
        (d.factorial : ℝ) ≤ (B : ℝ)^d := by
  obtain ⟨B, hB⟩ := uniform_lagrange_weight_envelope μ 1 hμ (by norm_num)
  refine ⟨B, ?_⟩
  intro d hd
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmul : ((d : ℝ) + 1) ≤ ((d : ℝ) + 1) * d := by
    simpa using mul_le_mul_of_nonneg_left hd' (by positivity : 0 ≤ (d : ℝ) + 1)
  apply le_trans _ (hB d hd)
  rw [one_pow, mul_one]
  gcongr

end CondFeffA

#print axioms CondFeffA.factorial_le_two_pow_mul_split
#print axioms CondFeffA.spacing_factorial_estimate
#print axioms CondFeffA.uniform_lagrange_weight_envelope
