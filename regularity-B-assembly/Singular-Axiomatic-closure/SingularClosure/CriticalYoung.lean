import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! Scalar Young bounds used after actual physical Holder estimates. -/
set_option autoImplicit false
namespace SingularClosure

theorem critical_young_square (ε x y : ℝ) (hε : 0 < ε) :
    x * y ≤ ε * y ^ 2 + x ^ 2 / (4 * ε) := by
  have heq : ε * y ^ 2 + x ^ 2 / (4 * ε) =
      (4 * ε ^ 2 * y ^ 2 + x ^ 2) / (4 * ε) := by
    field_simp [hε.ne']
    ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hε)).2
  nlinarith [sq_nonneg (2 * ε * y - x)]

/-- The L6-L3-L2 transport product produces the integrable Serrin coefficient. -/
theorem CRITICAL_TRANSPORT_YOUNG
    (ν A U W D : ℝ) (hν : 0 < ν) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hD : 0 ≤ D) :
    A * U * Real.sqrt W * Real.sqrt (D + W) * D ≤
      (ν / 2) * D ^ 2 +
        (8 * A ^ 4 * U ^ 4 / ν ^ 3 + A ^ 2 * U ^ 2 / ν) * W ^ 2 := by
  have hsW := Real.sq_sqrt hW
  have hsD := Real.sq_sqrt hD
  have hsplit : Real.sqrt (D + W) ≤ Real.sqrt D + Real.sqrt W := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sqrt_nonneg D, Real.sqrt_nonneg W]
  have hsq : (A * U * Real.sqrt W * Real.sqrt D) ^ 2 = A ^ 2 * U ^ 2 * W * D := by
    simp only [mul_pow, hsW, hsD]
    ring
  have h1 := critical_young_square (ν / 8) (A * U * Real.sqrt W * Real.sqrt D) D
    (by positivity)
  rw [hsq] at h1
  have h2 := critical_young_square (ν / 8) (2 * A ^ 2 * U ^ 2 * W / ν) D
    (by positivity)
  have h3 := critical_young_square (ν / 4) (A * U * W) D (by positivity)
  have h1' : A * U * Real.sqrt W * Real.sqrt D * D ≤
      (ν / 8) * D ^ 2 + (2 * A ^ 2 * U ^ 2 * W / ν) * D := by
    convert h1 using 1 <;> field_simp [hν.ne'] <;> ring
  have h2' : (2 * A ^ 2 * U ^ 2 * W / ν) * D ≤
      (ν / 8) * D ^ 2 + 8 * A ^ 4 * U ^ 4 * W ^ 2 / ν ^ 3 := by
    convert h2 using 1 <;> field_simp [hν.ne'] <;> ring
  have h3' : A * U * W * D ≤
      (ν / 4) * D ^ 2 + A ^ 2 * U ^ 2 * W ^ 2 / ν := by
    convert h3 using 1 <;> field_simp [hν.ne'] <;> ring
  calc
    _ ≤ A * U * Real.sqrt W * (Real.sqrt D + Real.sqrt W) * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsplit (by positivity)) hD
    _ = A * U * Real.sqrt W * Real.sqrt D * D + A * U * W * D := by
      calc
        _ = A * U * Real.sqrt W * Real.sqrt D * D +
            A * U * (Real.sqrt W) ^ 2 * D := by ring
        _ = _ := by rw [hsW]
    _ ≤ ((ν / 8) * D ^ 2 +
        ((ν / 8) * D ^ 2 + 8 * A ^ 4 * U ^ 4 * W ^ 2 / ν ^ 3)) +
        ((ν / 4) * D ^ 2 + A ^ 2 * U ^ 2 * W ^ 2 / ν) := by
      exact add_le_add (h1'.trans (add_le_add_left h2' _)) h3'
    _ = _ := by ring

end SingularClosure
