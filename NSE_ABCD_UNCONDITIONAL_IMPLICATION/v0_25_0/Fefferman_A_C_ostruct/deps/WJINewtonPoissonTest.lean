import WJINewtonFlux
import WJINewtonWeakGradient

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory Filter
open scoped ContDiff
noncomputable section

private theorem compact_test_partial_smooth {φ : RSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) : ContDiff ℝ ∞ (spatialDerivative i φ) :=
  (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply (g := fun _ => basisDirection i) contDiff_const

private theorem newtonGradientKernel_locallyIntegrable (i : Fin 3) :
    LocallyIntegrable (newtonGradientKernel i) volume := by
  have hd : Module.finrank ℝ RSpace = 3 := Module.finrank_fin_fun ℝ
  apply locallyIntegrable_of_norm_le_rpow (E := RSpace) (μ := volume)
    (f := newtonGradientKernel i) (C := (1 : ℝ)) (α := (2 : ℝ))
    (by rw [hd]; decide) (by rw [hd]; norm_num)
  · exact Eventually.of_forall fun z => by
      simpa only [one_mul, Real.rpow_neg (norm_nonneg z), Real.rpow_two] using
        newtonGradientKernel_majorized i z
  · exact (newtonGradientKernel_measurable i).aestronglyMeasurable

private theorem integral_three (q : Fin 3 → RSpace → ℝ) (hq : ∀ i, Integrable (q i)) :
    (∫ z, q 0 z + q 1 z + q 2 z) = (∫ z, q 0 z) + (∫ z, q 1 z) + (∫ z, q 2 z) := by
  calc
    _ = (∫ z, q 0 z + q 1 z) + (∫ z, q 2 z) :=
      integral_add (f := fun z => q 0 z + q 1 z) (g := q 2) ((hq 0).add (hq 1)) (hq 2)
    _ = _ := congrArg (fun t : ℝ => t + (∫ z, q 2 z)) (integral_add (hq 0) (hq 1))

/-- Fundamental solution of minus the package Laplacian at the origin,
    tested on arbitrary compact smooth scalar fields on its own space. -/
theorem wji_newton_fundamental_test {φ : RSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ z, newtonKernel z * (-laplacian realAnalysis φ z)) = φ 0 := by
  let d := fun i : Fin 3 => spatialDerivative i φ
  have hd (i : Fin 3) : ContDiff ℝ ∞ (d i) := compact_test_partial_smooth hφ i
  have hcd (i : Fin 3) : HasCompactSupport (d i) := hc.fderiv_apply ℝ (basisDirection i)
  let a := fun (i : Fin 3) (z : RSpace) => newtonKernel z * spatialDerivative i (d i) z
  let b := fun (i : Fin 3) (z : RSpace) => newtonGradientKernel i z * d i z
  have ha (i : Fin 3) : Integrable (a i) :=
    newtonKernel_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (compact_test_partial_smooth (hd i) i).continuous
      ((hcd i).fderiv_apply ℝ (basisDirection i))
  have hb (i : Fin 3) : Integrable (b i) :=
    (newtonGradientKernel_locallyIntegrable i).integrable_smul_right_of_hasCompactSupport
      (hd i).continuous (hcd i)
  have hparts (i : Fin 3) : (∫ z, a i z) = -(∫ z, b i z) :=
    wji_newtonKernel_weak_gradient i (hd i) (hcd i)
  have horder : (1 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
  calc
    (∫ z, newtonKernel z * (-laplacian realAnalysis φ z)) =
        ∫ z, -(a 0 z + a 1 z + a 2 z) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      change newtonKernel z * (-(spatialDerivative 0 (d 0) z +
          spatialDerivative 1 (d 1) z + spatialDerivative 2 (d 2) z)) = _
      dsimp only [a]
      ring
    _ = -((∫ z, a 0 z) + (∫ z, a 1 z) + ∫ z, a 2 z) := by
      rw [integral_neg]
      exact congrArg (fun t : ℝ => -t) (integral_three a ha)
    _ = (∫ z, b 0 z) + (∫ z, b 1 z) + ∫ z, b 2 z := by
      rw [hparts 0, hparts 1, hparts 2]
      ring
    _ = ∫ z, b 0 z + b 1 z + b 2 z := (integral_three b hb).symm
    _ = _ := newton_weak_flux_pkg (hφ.of_le horder) hc

end
end CondFeffA
