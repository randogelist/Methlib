import SingularClosure.CriticalPositiveTimeSeed
import SingularClosure.HighOrderEstimate

/-!
Actual Galerkin enstrophy estimates with an explicit integrable control.
The Fourier transport-square estimate is a retained, local analytic input;
it is not an assumed regularity or existence conclusion.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- Exact absorption of the actual Galerkin nonlinear enstrophy power. -/
theorem GALERKIN_ENSTROPHY_RATE_OF_TRANSPORT_SQUARE
    (ν : ℝ) (hν : 0 < ν) (N : ℕ) (c : FourierCoeff)
    (R : ℝ) (hR : 0 ≤ R)
    (hpower : coefficientEnstrophyNonlinearPower N c ^ 2 ≤
      R * coefficientDissipation N c * coefficientLaplacianSquare N c) :
    (-2 * ν) * coefficientLaplacianSquare N c -
        2 * coefficientEnstrophyNonlinearPower N c +
        ν * coefficientLaplacianSquare N c ≤
      (R / ν) * coefficientDissipation N c := by
  have hD := coefficientDissipation_nonneg N c
  have hZ := coefficientLaplacianSquare_nonneg N c
  have hsquare : abs (coefficientEnstrophyNonlinearPower N c) ^ 2 ≤
      (ν * coefficientLaplacianSquare N c) *
        ((R / ν) * coefficientDissipation N c) := by
    rw [sq_abs]
    calc
      _ ≤ R * coefficientDissipation N c * coefficientLaplacianSquare N c := hpower
      _ = _ := by field_simp [ne_of_gt hν] <;> ring
  have habs := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hν.le hZ) (mul_nonneg (div_nonneg hR hν.le) hD) hsquare
  have hneg := neg_le_abs (coefficientEnstrophyNonlinearPower N c)
  nlinarith

/-- A uniform integral of the concrete transport control gives a uniform
enstrophy and Laplacian budget for every actual Galerkin solution. -/
theorem GALERKIN_ENSTROPHY_ACCUMULATION_OF_CONTROL
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field)
    (R : ∀ N : ℕ, GalerkinSolution ν (a N) N → ℝ → ℝ)
    (E₀ S : ℝ)
    (hRcont : ∀ N g, ContinuousOn (R N g) (Ici 0))
    (hRnonneg : ∀ N g t, 0 ≤ t → 0 ≤ R N g t)
    (hpower : ∀ N g t, 0 ≤ t →
      coefficientEnstrophyNonlinearPower N (g.coeff t) ^ 2 ≤
        R N g t * coefficientDissipation N (g.coeff t) *
          coefficientLaplacianSquare N (g.coeff t))
    (hinitial : ∀ N g, coefficientDissipation N (g.coeff 0) ≤ E₀)
    (hbudget : ∀ N g T, 0 ≤ T → (∫ t in (0 : ℝ)..T, R N g t) ≤ S) :
    ∀ T : ℝ, 0 ≤ T → ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      ∀ t ∈ Icc (0 : ℝ) T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s)) ≤
            E₀ * Real.exp (S / ν) := by
  intro T hT N g
  let y : ℝ → ℝ := fun t => coefficientDissipation N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (coefficientLaplacianSquare N (g.coeff t))
  let d : ℝ → ℝ := fun t => (-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
    2 * coefficientEnstrophyNonlinearPower N (g.coeff t)
  let A : ℝ → ℝ := fun t => (ν⁻¹) * R N g t
  have hy : ContinuousOn y (Icc 0 T) :=
    g.coefficientDissipation_continuousOn.mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      g.coefficientLaplacianSquare_continuousOn).mono (fun t ht => ht.1)
  have hA : ContinuousOn A (Icc 0 T) :=
    continuousOn_const.mul ((hRcont N g).mono (fun t ht => ht.1))
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t := by
    intro t ht
    exact (g.coefficientEnstrophy_identity ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hl : ∀ t ∈ Ioo 0 T, d t + ν * z t ^ 2 ≤ A t * y t := by
    intro t ht
    have h := GALERKIN_ENSTROPHY_RATE_OF_TRANSPORT_SQUARE ν hν N (g.coeff t)
      (R N g t) (hRnonneg N g t ht.1.le) (hpower N g t ht.1.le)
    simpa only [d, z, y, A,
      Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff t)),
      div_eq_mul_inv, mul_comm (R N g t) ν⁻¹] using h
  have hb : (∫ t in (0 : ℝ)..T, A t) ≤ S / ν := by
    dsimp only [A]
    rw [intervalIntegral.integral_const_mul]
    have h := mul_le_mul_of_nonneg_left (hbudget N g T hT) (inv_nonneg.mpr hν.le)
    simpa only [div_eq_mul_inv, mul_comm S ν⁻¹] using h
  have h := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET hν.le hT hy hz hA
    (fun t _ => coefficientDissipation_nonneg N (g.coeff t))
    (fun t ht => mul_nonneg (inv_nonneg.mpr hν.le) (hRnonneg N g t ht.1))
    (hinitial N g) hd hl hb
  intro t ht
  have hzsq (s : ℝ) : z s ^ 2 = coefficientLaplacianSquare N (g.coeff s) :=
    Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff s))
  simpa only [y, hzsq] using h t ht

end
end QuasiFeffermanB
