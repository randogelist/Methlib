import QuasiFeffermanB.RegularReference
import QuasiFeffermanB.PhysicalH1Admission
import QuasiFeffermanB.CaloricH1Regularity

/-! Conversion of the concrete spectral caloric budget into the exact
physical H1 restart admission. The budget is an explicit premise here;
the final unconditional theorem must supply its independent proof. -/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem EXACT_H1_ADMISSION_OF_SPECTRAL_CALORIC_BUDGET
    (ν : ℝ) (hν : 0 < ν)
    (hcaloric : ∀ b : CriticalSobolev 2,
      SpectralReality (criticalCoeff 2 b) →
      SpectralSolenoidal (criticalCoeff 2 b) →
      SpectralMeanZero (criticalCoeff 2 b) →
      ‖criticalSobolevLower 1 2 (by norm_num) b‖ ^ 2 < 2 * Real.pi * ν ^ 2 →
      ∃ S : ℝ, ∀ (N : ℕ)
        (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 b)) N),
        ∀ T : ℝ, 0 ≤ T →
          (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S) :
    ExactH1Admission ν := by
  intro v D hv ha hsmall
  have hrep : (criticalL2Representative v : Field)
      =ᵐ[volume.restrict unitCube] v := by
    rw [criticalL2Representative_eq _ hv.velocity_L2]
    exact hv.velocity_L2.coeFn_toLp
  have hcoeff := criticalCube_datumFourierCoeff_congr_ae hrep
  have hconstraints := ha.fourier_constraints
  rw [hcoeff] at hconstraints
  obtain ⟨hreal, hsol, hzero⟩ := hconstraints
  let b : CriticalSobolev 2 := physicalH1SobolevDatum hv hzero
  have hbcoeff : criticalCoeff 2 b = datumFourierCoeff v :=
    physicalH1SobolevDatum_coeff hv hzero
  have hbr : SpectralReality (criticalCoeff 2 b) := by rw [hbcoeff]; exact hreal
  have hbs : SpectralSolenoidal (criticalCoeff 2 b) := by rw [hbcoeff]; exact hsol
  have hbz : SpectralMeanZero (criticalCoeff 2 b) := by rw [hbcoeff]; exact hzero
  have hbsmall : ‖criticalSobolevLower 1 2 (by norm_num) b‖ ^ 2 <
      2 * Real.pi * ν ^ 2 := by
    rw [physicalH1SobolevDatum_half_norm_sq]
    have h := (ENNReal.toReal_lt_toReal (physicalH1_halfEnergy_ne_top hv)
      ENNReal.ofReal_ne_top).2 hsmall
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi * ν ^ 2 by positivity)] using h
  obtain ⟨S, hS⟩ := hcaloric b hbr hbs hbz hbsmall
  obtain ⟨L, _hNSE, htrace, hSerrin, _hD, _hcompare⟩ :=
    CALORIC_H1_REGULARITY_OF_FINITE_CHI0_BUDGET ν hν b hbr hbs hbz S hS
  have hbphys : criticalInitialPhysicalL2
      (criticalSobolevLower 1 2 (by norm_num) b) = criticalL2Representative v :=
    physicalH1SobolevDatum_physicalL2 hv hzero
  rw [hbphys] at htrace
  exact ⟨⟨L, htrace, hSerrin⟩⟩

end
end QuasiFeffermanB
