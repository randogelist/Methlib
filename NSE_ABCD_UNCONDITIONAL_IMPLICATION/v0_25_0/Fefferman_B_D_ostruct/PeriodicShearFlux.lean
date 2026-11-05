import ConcreteABCDUnifiedClosure
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

namespace CondFeffB
open Fefferman Fefferman.ConcreteReal MeasureTheory Set
open scoped BigOperators

noncomputable section

def differenceFlux (ν : ℝ) (U W : RSpace → RVector) (P : RSpace → ℝ)
    (x : RSpace) (j : Fin 3) : ℝ :=
  2 * ν * (∑ i, W x i * spatialDerivative j (fun y => W y i) x) -
    U x j * (∑ i, (W x i) ^ 2) - 2 * P x * W x j

def fluxDivergence (F : RSpace → RVector) (x : RSpace) : ℝ :=
  ∑ j, spatialDerivative j (fun y => F y j) x

def fluxDerivativeTerm (ν : ℝ) (U W : RVector) (P : ℝ)
    (dU dW d2W : Fin 3 → RVector) (dP : RVector) (j : Fin 3) : ℝ :=
  2 * ν * (∑ i : Fin 3, ((dW j i) ^ 2 + W i * d2W j i)) -
    dU j j * (∑ i, (W i) ^ 2) - U j * (∑ i, 2 * W i * dW j i) -
    2 * dP j * W j - 2 * P * dW j j

private theorem basis_eq_single (j : Fin 3) :
    basisDirection j = Pi.single j (1 : ℝ) := by
  funext i
  by_cases h : i = j
  · subst i
    simp [basisDirection]
  · simp [basisDirection, h]

private theorem oppositeFaces (j : Fin 3) (y : Fin 2 → ℝ) :
    unitShift realAnalysis (j.insertNth (-(1 / 2 : ℝ)) y) j =
      j.insertNth (1 / 2 : ℝ) y := by
  funext i
  by_cases h : i = j
  · subst i
    norm_num [unitShift, realAnalysis]
  · rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
    simp [unitShift, Fin.succAbove_ne]

/-- The flux through opposite faces cancels on the unit periodic cell. -/
theorem integral_periodic_fluxDivergence (F : RSpace → RVector)
    (hC : ∀ j, ContDiff ℝ 1 (fun x => F x j))
    (hper : ∀ x j, F (unitShift realAnalysis x j) j = F x j) :
    (∫ x in Icc (fun _ : Fin 3 => -(1 / 2 : ℝ)) (fun _ : Fin 3 => (1 / 2 : ℝ)),
      fluxDivergence F x) = 0 := by
  let lo : RSpace := fun _ => -(1 / 2 : ℝ)
  let hi : RSpace := fun _ => (1 / 2 : ℝ)
  let DF := fun (j : Fin 3) (x : RSpace) => fderiv ℝ (fun y => F y j) x
  have hle : lo ≤ hi := by intro i; norm_num [lo, hi]
  have hdiv : Continuous (fun x : RSpace => ∑ j : Fin 3, DF j x (Pi.single j (1 : ℝ))) := by
    apply continuous_finsetSum
    intro j _
    exact ((hC j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (n := 2) lo hi hle (fun j x => F x j) DF ∅ Set.countable_empty
    (fun j => (hC j).continuous.continuousOn)
    (fun x _ j => ((hC j).differentiable one_ne_zero x).hasFDerivAt)
    hdiv.continuousOn.integrableOn_Icc
  change (∫ x in Icc lo hi, fluxDivergence F x) = 0
  simp only [fluxDivergence, spatialDerivative, basis_eq_single]
  change (∫ x in Icc lo hi, ∑ j : Fin 3, DF j x (Pi.single j 1)) = 0
  rw [h]
  apply Finset.sum_eq_zero
  intro j _
  have hf : (fun y : Fin 2 → ℝ => F (j.insertNth (hi j) y) j) =
      (fun y : Fin 2 → ℝ => F (j.insertNth (lo j) y) j) := by
    funext y
    change F (j.insertNth (1 / 2 : ℝ) y) j = F (j.insertNth (-(1 / 2 : ℝ)) y) j
    rw [← oppositeFaces j y]
    exact hper _ j
  rw [hf, sub_self]

set_option maxHeartbeats 1200000 in
/-- Local energy balance after product differentiation. The two cancellations
use incompressibility of the candidate and of its difference with the shear. -/
theorem localEnergyBalance (ν g P : ℝ) (U W dt dP : RVector)
    (dU dW d2W : Fin 3 → RVector)
    (hU : (∑ j : Fin 3, dU j j) = 0) (hW : (∑ j : Fin 3, dW j j) = 0)
    (heq : ∀ i : Fin 3, dt i + (∑ j, U j * dW j i) +
        (if i = 0 then W 1 * g else 0) = ν * (∑ j, d2W j i) - dP i) :
    (∑ i, 2 * W i * dt i) =
      (∑ j, fluxDerivativeTerm ν U W P dU dW d2W dP j) -
      2 * ν * (∑ j, ∑ i, (dW j i) ^ 2) - 2 * g * W 0 * W 1 := by
  have hi1 : (1 : Fin 3) ≠ 0 := by decide
  have hi2 : (2 : Fin 3) ≠ 0 := by decide
  have h0 : dt 0 + (∑ j : Fin 3, U j * dW j 0) + W 1 * g =
      ν * (∑ j : Fin 3, d2W j 0) - dP 0 := by
    simpa using heq 0
  have h1 : dt 1 + (∑ j : Fin 3, U j * dW j 1) =
      ν * (∑ j : Fin 3, d2W j 1) - dP 1 := by
    simpa [hi1] using heq 1
  have h2 : dt 2 + (∑ j : Fin 3, U j * dW j 2) =
      ν * (∑ j : Fin 3, d2W j 2) - dP 2 := by
    simpa [hi2] using heq 2
  simp only [Fin.sum_univ_three] at h0 h1 h2 hU hW
  simp only [fluxDerivativeTerm, Fin.sum_univ_three]
  linear_combination 2 * W 0 * h0 + 2 * W 1 * h1 + 2 * W 2 * h2 +
    ((W 0)^2 + (W 1)^2 + (W 2)^2) * hU + 2 * P * hW

theorem shearProduction_le (g L : ℝ) (W : RVector) (hg : |g| ≤ L) :
    -(2 * g * W 0 * W 1) ≤ L * ∑ i, (W i)^2 := by
  have hquad : 2 * |W 0| * |W 1| ≤ ∑ i, (W i)^2 := by
    rw [Fin.sum_univ_three]
    nlinarith [sq_nonneg (|W 0| - |W 1|), sq_abs (W 0), sq_abs (W 1),
      sq_nonneg (W 2)]
  calc
    -(2 * g * W 0 * W 1) ≤ |2 * g * W 0 * W 1| := neg_le_abs _
    _ = |g| * (2 * |W 0| * |W 1|) := by
      have htwo : |(2 : ℝ)| = 2 := by norm_num
      simp only [abs_mul, htwo]
      ring
    _ ≤ L * ∑ i, (W i)^2 := mul_le_mul hg hquad (by positivity) ((abs_nonneg _).trans hg)

end
end CondFeffB
