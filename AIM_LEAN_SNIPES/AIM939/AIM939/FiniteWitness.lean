import AIM939.Core

/-!
Exact midpoint counterexample for the four-variable AIM939 instance.

All root comparisons follow from rational fourth-power certificates and
monotonicity of the real fourth root. No multivariable differentiation is used.
Prepared candidate: matching external compilation and axiom audit are pending.
-/

noncomputable section

namespace AIM939

def xMinus : Point :=
  ![(1 / 200 : ℝ), (397 / 100 : ℝ), (1 / 200 : ℝ), (1 / 200 : ℝ)]

def xMid : Point :=
  ![(1 / 100 : ℝ), (4 : ℝ), (1 / 100 : ℝ), (1 / 100 : ℝ)]

def xPlus : Point :=
  ![(3 / 200 : ℝ), (403 / 100 : ℝ), (3 / 200 : ℝ), (3 / 200 : ℝ)]

def qMinus : ℝ := 17392403 / 10000000
def qMid : ℝ := 17522350 / 10000000
def qPlus : ℝ := 17652309 / 10000000

theorem xMinus_mem_orthant : xMinus ∈ orthant := by
  change ∀ i : Fin 4, 0 < xMinus i
  intro i
  fin_cases i <;> norm_num [xMinus]

theorem xMid_mem_orthant : xMid ∈ orthant := by
  change ∀ i : Fin 4, 0 < xMid i
  intro i
  fin_cases i <;> norm_num [xMid]

theorem xPlus_mem_orthant : xPlus ∈ orthant := by
  change ∀ i : Fin 4, 0 < xPlus i
  intro i
  fin_cases i <;> norm_num [xPlus]

theorem xMid_eq_midpoint :
    xMid = (1 / 2 : ℝ) • xMinus + (1 / 2 : ℝ) • xPlus := by
  funext i
  fin_cases i <;>
    norm_num [xMid, xMinus, xPlus, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem f_xMinus : f xMinus = (7320291897 / 800000000 : ℝ) := by
  norm_num [f, sigma1, sigma2, sigma3, sigma4, xMinus,
    Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

theorem f_xMid : f xMid = (9426909 / 1000000 : ℝ) := by
  norm_num [f, sigma1, sigma2, sigma3, sigma4, xMid,
    Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

theorem f_xPlus : f xPlus = (7767765381 / 800000000 : ℝ) := by
  norm_num [f, sigma1, sigma2, sigma3, sigma4, xPlus,
    Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

theorem qMinus_pow4_lt : qMinus ^ (4 : ℕ) < f xMinus := by
  rw [f_xMinus]
  norm_num [qMinus]

theorem qMid_pow4_gt : f xMid < qMid ^ (4 : ℕ) := by
  rw [f_xMid]
  norm_num [qMid]

theorem qPlus_pow4_lt : qPlus ^ (4 : ℕ) < f xPlus := by
  rw [f_xPlus]
  norm_num [qPlus]

theorem rational_midpoint_gap :
    (qMinus + qPlus) / 2 - qMid = (3 / 5000000 : ℝ) := by
  norm_num [qMinus, qMid, qPlus]

theorem rational_midpoint_gt : qMid < (qMinus + qPlus) / 2 := by
  norm_num [qMinus, qMid, qPlus]

/-- The principal real fourth root cancels a fourth power of a nonnegative real. -/
theorem witness_rootQuarter_pow4 {q : ℝ} (hq : 0 ≤ q) :
    rootQuarter (q ^ (4 : ℕ)) = q := by
  unfold rootQuarter
  simpa only [one_div, Nat.cast_ofNat] using
    (Real.pow_rpow_inv_natCast hq (by norm_num : (4 : ℕ) ≠ 0))

theorem witness_lower_from_pow4 {q u : ℝ}
    (hq : 0 ≤ q) (h : q ^ (4 : ℕ) < u) :
    q < rootQuarter u := by
  have hh : rootQuarter (q ^ (4 : ℕ)) < rootQuarter u :=
    Real.rpow_lt_rpow (pow_nonneg hq 4) h (by norm_num : (0 : ℝ) < 1 / 4)
  simpa only [witness_rootQuarter_pow4 hq] using hh

theorem witness_upper_from_pow4 {q u : ℝ}
    (hu : 0 ≤ u) (hq : 0 ≤ q) (h : u < q ^ (4 : ℕ)) :
    rootQuarter u < q := by
  have hh : rootQuarter u < rootQuarter (q ^ (4 : ℕ)) :=
    Real.rpow_lt_rpow hu h (by norm_num : (0 : ℝ) < 1 / 4)
  simpa only [witness_rootQuarter_pow4 hq] using hh

theorem qMinus_lt_root : qMinus < rootQuarter (f xMinus) := by
  exact witness_lower_from_pow4 (by norm_num [qMinus]) qMinus_pow4_lt

theorem root_mid_lt_qMid : rootQuarter (f xMid) < qMid := by
  apply witness_upper_from_pow4
  · exact le_of_lt (f_pos xMid_mem_orthant)
  · norm_num [qMid]
  · exact qMid_pow4_gt

theorem qPlus_lt_root : qPlus < rootQuarter (f xPlus) := by
  exact witness_lower_from_pow4 (by norm_num [qPlus]) qPlus_pow4_lt

/-- A strict midpoint failure at three explicit points of the positive orthant. -/
theorem midpoint_violation :
    rootQuarter (f xMid) <
      (rootQuarter (f xMinus) + rootQuarter (f xPlus)) / 2 := by
  have hm := qMinus_lt_root
  have hp := qPlus_lt_root
  have h0 := root_mid_lt_qMid
  have hgap := rational_midpoint_gt
  linarith

/-- The full fourth-root concavity conclusion of the conjecture fails. -/
theorem not_concaveOn_rootQuarter_f :
    ¬ ConcaveOn ℝ orthant (fun x => rootQuarter (f x)) := by
  intro hconc
  have hj := hconc.2 xMinus_mem_orthant xPlus_mem_orthant
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [← xMid_eq_midpoint] at hj
  simp only [smul_eq_mul] at hj
  have hbad := midpoint_violation
  linarith

end AIM939
