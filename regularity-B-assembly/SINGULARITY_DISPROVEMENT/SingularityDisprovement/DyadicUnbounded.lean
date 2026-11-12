import SingularityDisprovement.Admission
import SingularityDisprovement.Dyadic
import SingularityDisprovement.FejerKernel

/-! Essential unboundedness of the actual native dyadic datum.

The proof uses positive, normalized finite Fejer tests. Thus divergence of
positive Fourier sums forces positive-measure physical superlevel sets;
no conclusion is inferred from the value of a series at a single point.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ENNReal Topology

namespace SingularityDisprovement
noncomputable section

def dyadicAxisCoefficient (ν : ℝ) (z : ℤ) : ℝ :=
  ν / 4 * dyadicAmplitude z.natAbs

theorem dyadicAxisCoefficient_nonneg {ν : ℝ} (hν : 0 < ν) (z : ℤ) :
    0 ≤ dyadicAxisCoefficient ν z := by
  exact mul_nonneg (by positivity) (dyadicAmplitude_nonneg _)

theorem dyadicAxisCoefficient_not_summable {ν : ℝ} (hν : 0 < ν) :
    ¬ Summable (fun n : ℕ => dyadicAxisCoefficient ν (n : ℤ)) := by
  intro h
  apply dyadicAmplitude_not_summable
  apply (summable_mul_left_iff (show ν / 4 ≠ 0 by positivity)).mp
  simpa only [dyadicAxisCoefficient, Int.natAbs_natCast] using h

/-- Recovery is on the native L2 representative, not on a postulated series. -/
theorem dyadicSeed_physical_axis_coefficient (ν : ℝ) (z : ℤ) :
    (datumFourierCoeff (physicalL2 (dyadicSeed ν) : Field) (fejerAxis z) 0).re =
      dyadicAxisCoefficient ν z := by
  rw [physicalL2_eq_native,
    criticalInitialPhysicalL2_fourierCoeff (dyadicSeed ν)
      (dyadicSeed_sigma ν).reality (dyadicSeed_sigma ν).mean_zero,
    dyadicSeed_coeff]
  simp [dyadicCoeff, fejerAxis, dyadicAxisCoefficient]

/-- The literal R08 endpoint: every finite density superlevel has positive
physical measure for the constructed, nonzero native Hhalf datum. -/
theorem dyadicSeed_essUnbounded (ν : ℝ) (hν : 0 < ν) :
    EssUnbounded (dyadicSeed ν) := by
  intro M hM
  by_contra hpos
  have hzero : (volume.restrict unitCube)
      {x | M < kineticDensity (dyadicSeed ν) x} = 0 :=
    le_antisymm (le_of_not_gt hpos) (zero_le _)
  have hle : ∀ᵐ x ∂volume.restrict unitCube,
      kineticDensity (dyadicSeed ν) x ≤ M := by
    apply ae_iff.mpr
    simpa only [not_le] using hzero
  have hcomponent : ∀ᵐ x ∂volume.restrict unitCube,
      physicalL2 (dyadicSeed ν) x 0 ≤ M + 1 := by
    filter_upwards [hle] with x hx
    have hn : ‖physicalL2 (dyadicSeed ν) x‖ ≤ M + 1 := by
      change ‖physicalL2 (dyadicSeed ν) x‖ ^ 2 / 2 ≤ M at hx
      nlinarith [sq_nonneg (‖physicalL2 (dyadicSeed ν) x‖ - 1)]
    have hc : physicalL2 (dyadicSeed ν) x 0 ≤ ‖physicalL2 (dyadicSeed ν) x‖ := by
      calc
        _ ≤ |physicalL2 (dyadicSeed ν) x 0| := le_abs_self _
        _ = ‖physicalL2 (dyadicSeed ν) x 0‖ := (Real.norm_eq_abs _).symm
        _ ≤ _ := PiLp.norm_apply_le _ _
    exact hc.trans hn
  have hbound : ∀ N : ℕ, 0 < N →
      fejerCoefficientAverage (dyadicAxisCoefficient ν) N ≤ M + 1 := by
    intro N hN
    have h := fejerAverage_le_of_component_ae_le
      (physicalL2 (dyadicSeed ν)) (M + 1) hcomponent N hN
    simpa only [dyadicSeed_physical_axis_coefficient] using h
  exact dyadicAxisCoefficient_not_summable hν
    (summable_of_positive_fejerAverage_bounded (dyadicAxisCoefficient ν)
      (dyadicAxisCoefficient_nonneg hν) (M + 1) (by linarith) hbound)

end
end SingularityDisprovement
