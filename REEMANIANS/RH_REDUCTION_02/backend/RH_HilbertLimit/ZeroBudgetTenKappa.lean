import RH_HilbertLimit.ZeroBudgetTenCenter

/-!
# A rational upper bound for the actual normalization scalar

The previously constructed normalized theta product, evaluated at one
quarter, controls its positive reciprocal-scale trace. The bound on the
pole-subtracted completed zeta function at one half supplies a lower bound
for the norm of theta at zero. Neither a sign for that completed-zeta value
nor an RH assumption is used.

Prepared by source inspection only; native Lean compilation and axiom audit
remain pending.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Topology
open Filter

namespace RH_HilbertLimit

open AngularMaster

/-- The linear contribution of nonnegative real parts is retained in every
finite product of the corresponding affine complex factors. -/
private theorem zeroBudgetTen_finite_product_trace_lower
    {ι : Type*} (f : ι → ℂ) (hf : ∀ i, 0 ≤ (f i).re) (F : Finset ι) :
    1 + ∑ i ∈ F, (f i).re ≤ ‖∏ i ∈ F, (1 + f i)‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, norm_mul]
      have hsum : 0 ≤ ∑ j ∈ F, (f j).re :=
        Finset.sum_nonneg (fun j _hj => hf j)
      have hfactor : 1 + (f i).re ≤ ‖1 + f i‖ := by
        simpa only [Complex.add_re, Complex.one_re] using
          Complex.re_le_norm (1 + f i)
      calc
        1 + ((f i).re + ∑ j ∈ F, (f j).re) ≤
            (1 + (f i).re) * (1 + ∑ j ∈ F, (f j).re) := by
          nlinarith only [mul_nonneg (hf i) hsum]
        _ ≤ ‖1 + f i‖ * ‖∏ j ∈ F, (1 + f j)‖ :=
          mul_le_mul hfactor ih (by linarith) (norm_nonneg _)

/-- The positive actual reciprocal trace supplies a lower bound on the
norm of the quarter-point canonical product. -/
theorem zeroBudgetTen_product_norm_ge_one_add_kappa_quarter :
    1 + actualKappa / 4 ≤
      ‖∏' i : ActualPairIndex, (1 + (1 / 4 : ℂ) / actualComplexScale i)‖ := by
  classical
  have hreal (i : ActualPairIndex) :
      ((1 / 4 : ℂ) / actualComplexScale i).re =
        (1 / 4 : ℝ) * ((actualComplexScale i)⁻¹).re := by
    rw [div_eq_mul_inv, Complex.mul_re]
    norm_num
  have hs0 := actualComplexScale_inv_re_summable.hasSum.mul_left (1 / 4 : ℝ)
  rw [← actualKappa_eq_canonical_trace] at hs0
  have hs : HasSum
      (fun i : ActualPairIndex => ((1 / 4 : ℂ) / actualComplexScale i).re)
      (actualKappa / 4) := by
    simp_rw [hreal]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hs0
  have hsumlim : Tendsto
      (fun F : Finset ActualPairIndex =>
        ∑ i ∈ F, ((1 / 4 : ℂ) / actualComplexScale i).re)
      atTop (𝓝 (actualKappa / 4)) := hs
  have hsumone : Tendsto
      (fun F : Finset ActualPairIndex =>
        1 + ∑ i ∈ F, ((1 / 4 : ℂ) / actualComplexScale i).re)
      atTop (𝓝 (1 + actualKappa / 4)) :=
    tendsto_const_nhds.add hsumlim
  have hprodlim : Tendsto
      (fun F : Finset ActualPairIndex =>
        ∏ i ∈ F, (1 + (1 / 4 : ℂ) / actualComplexScale i))
      atTop (𝓝 (∏' i : ActualPairIndex,
        (1 + (1 / 4 : ℂ) / actualComplexScale i))) :=
    (actual_complexScaleProduct_multipliable (1 / 4 : ℂ)).hasProd
  apply le_of_tendsto_of_tendsto hsumone hprodlim.norm
  exact Filter.Eventually.of_forall (fun F =>
    zeroBudgetTen_finite_product_trace_lower
      (fun i : ActualPairIndex => (1 / 4 : ℂ) / actualComplexScale i)
      (fun i => by
        rw [hreal]
        exact mul_nonneg (by norm_num) (actualInverseScale_re_pos i).le) F)

/-- The center estimate controls the norm of theta at zero by a reverse
triangle inequality. No reality or positivity premise for completed zeta
is needed. -/
theorem zeroBudgetTen_theta_zero_norm_ge_207_418 :
    (207 / 418 : ℝ) ≤ ‖AWPIRH.theta 0‖ := by
  have hform :
      2 * AWPIRH.theta 0 +
        (1 / 4 : ℂ) * completedRiemannZeta₀ (1 / 2 : ℂ) = 1 := by
    norm_num [AWPIRH.theta, AWPIRH.centeredXi, AWPIRH.xi] <;> ring
  have htriangle := norm_add_le (2 * AWPIRH.theta 0)
    ((1 / 4 : ℂ) * completedRiemannZeta₀ (1 / 2 : ℂ))
  rw [hform, norm_one, norm_mul, norm_mul] at htriangle
  norm_num at htriangle
  have hcenter := zeroBudget_completedZeta0_half_norm_le_eight_209
  nlinarith

/-- The exact normalization scalar is bounded independently of RH. -/
theorem zeroBudget_actualKappa_le_eight_207 :
    actualKappa ≤ (8 / 207 : ℝ) := by
  have hquarter : AWPIRH.theta (1 / 4 : ℂ) = (1 / 2 : ℂ) := by
    have h := AWPIRH.theta_square (1 / 2 : ℂ)
    norm_num [AWPIRH.centeredXi, AWPIRH.xi] at h
    exact h
  have hfactor := congrArg (fun z : ℂ => ‖z‖)
    (actual_theta_normalized_complex_factorization (1 / 4 : ℂ))
  rw [hquarter, norm_mul] at hfactor
  norm_num at hfactor
  have hkpos := actualKappa_pos
  have hlower := mul_le_mul zeroBudgetTen_theta_zero_norm_ge_207_418
    zeroBudgetTen_product_norm_ge_one_add_kappa_quarter
    (by positivity : 0 ≤ 1 + actualKappa / 4)
    (norm_nonneg (AWPIRH.theta 0))
  rw [← hfactor] at hlower
  nlinarith

end RH_HilbertLimit
