import QuasiFeffermanB.CaloricGalerkinMajorant
import QuasiFeffermanB.CaloricFourierEstimate
import QuasiFeffermanB.FiniteCaloricSchur
import QuasiFeffermanB.ExactAdmission

/-! The exact numerical H1 restart admission. The finite Galerkin heat
estimate, nonlinear multiplier, time convolution, scalar barrier, and
positive-time regularity construction are all supplied by proved edges.
External compiler and theorem-level axiom evidence are required for promotion. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem SPECTRAL_H1_CALORIC_BUDGET
    (ν : ℝ) (hν : 0 < ν) (b : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 b))
    (_hsol : SpectralSolenoidal (criticalCoeff 2 b))
    (_hzero : SpectralMeanZero (criticalCoeff 2 b))
    (hsmall : ‖criticalSobolevLower 1 2 (by norm_num) b‖ ^ 2 < 2 * Real.pi * ν ^ 2) :
    ∃ S : ℝ, ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 b)) N),
      ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S := by
  let a : CriticalSobolev 1 := criticalSobolevLower 1 2 (by norm_num) b
  let B : ℝ := ‖a‖ ^ 2 / (4 * Real.pi)
  have hB : 0 ≤ B := div_nonneg (sq_nonneg _) (by positivity)
  have hBsmall : B < ν ^ 2 / 2 := by
    apply (div_lt_iff₀ (show 0 < 4 * Real.pi by positivity)).2
    change ‖a‖ ^ 2 < 2 * Real.pi * ν ^ 2 at hsmall
    nlinarith
  refine ⟨4 * B / ν, ?_⟩
  intro N g T hT
  apply GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC g hν B hB hBsmall
    (fun k hk t ht => COEFFICIENT_TRANSPORT_SHARP_EUCLIDEAN N (g.coeff t)
      (g.mode_support t ht) (g.solenoidal t ht) k (((mem_cutoffModes_iff N k).mp hk).2.1))
    ?_ T hT
  apply (FINITE_CALORIC_SCHUR N (g.coeff 0)).trans
  apply div_le_div_of_nonneg_right _ (show 0 ≤ 4 * Real.pi by positivity)
  rw [criticalGalerkin_initial_coeff hreal g, criticalEnergy_cutoffCoeff]
  have hac : criticalCoeff 1 a = criticalCoeff 2 b := criticalSobolevLower_coeff _ _ _ _
  rw [← hac]
  exact criticalEnergy_le_norm_sq 1 N a

/-- Exact physical H1 admission with no undisclosed analytic or certificate
premise. This is a candidate until its matching external audit passes. -/
theorem EXACT_H1_ADMISSION_UNCONDITIONAL (ν : ℝ) (hν : 0 < ν) : ExactH1Admission ν := by
  exact EXACT_H1_ADMISSION_OF_SPECTRAL_CALORIC_BUDGET ν hν
    (SPECTRAL_H1_CALORIC_BUDGET ν hν)

end
end QuasiFeffermanB
