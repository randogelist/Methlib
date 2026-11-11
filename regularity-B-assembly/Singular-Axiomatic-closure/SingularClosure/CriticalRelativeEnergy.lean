import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalSmoothEnergy

/-! Physical relative energy derived from the genuine weak momentum equation,
standard Leray--Hopf energy inequality and the classical energy equality.
The nonlinear term is still the exact weak/classical cross term. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

/-- Relative energy at any admissible positive initial time.  The only energy
hypothesis `henergy` is the ordinary Leray--Hopf energy inequality at that time;
the cross identity and all diffusion identities are proved independently. -/
theorem CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_RAW
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
    (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
    (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + gradient (p r) x =
        ν • laplacian (u r) x)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)) :
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) - 2 * (∫ r in s..t,
        criticalWeakTransport (v r) (u r) - physicalFieldInner (v r) (convection (u r))) := by
  have ht : 0 < t := hs.trans_le hst
  have hclassical := CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY ν u p hu hp hpp hNSE hν s t hs hst
  have hcross := CRITICAL_WEAK_CLASSICAL_CROSS_IDENTITY ν v u p hv.momentum hu
    hp hpp hNSE s t hs hst
  obtain ⟨hTime, hLap, hTransport⟩ := hv.momentum.test_integrable u hu s t hs hst
  have hDv : IntervalIntegrable (fun r => criticalGradientEnergy (G r)) volume s t := by
    apply (hv.dissipation_integrable t ht).mono_set
    rw [uIcc_of_le hst, uIcc_of_le ht.le]
    exact Icc_subset_Icc hs.le le_rfl
  have hN : IntervalIntegrable (fun r => criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) volume s t := by
    apply (hcross.1.sub (hLap.const_mul (2 * ν))).congr
    intro r _
    ring
  have hcross_eq : physicalFieldInner (v t) (u t) - physicalFieldInner (v s) (u s) =
      2 * ν * (∫ r in s..t, physicalFieldInner (v r) (laplacian (u r))) +
        (∫ r in s..t, criticalWeakTransport (v r) (u r) -
          physicalFieldInner (v r) (convection (u r))) := by
    rw [hcross.2]
    calc
      _ = ∫ r in s..t,
          (2 * ν) * physicalFieldInner (v r) (laplacian (u r)) +
            (criticalWeakTransport (v r) (u r) - physicalFieldInner (v r) (convection (u r))) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hLap.const_mul (2 * ν)) hN,
          intervalIntegral.integral_const_mul]
  have hH1 : ∀ᵐ r ∂volume.restrict (Ioc s t), CriticalPhysicalH1 (v r) (G r) :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc hs.le le_rfl) (hv.spatial_H1 t ht)
  have hdiff : (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) =ᵐ[
      volume.restrict (uIoc s t)]
      (fun r => criticalGradientEnergy (G r) + physicalDissipation (u r) +
        2 * physicalFieldInner (v r) (laplacian (u r))) := by
    rw [uIoc_of_le hst]
    filter_upwards [hH1, ae_restrict_mem measurableSet_Ioc] with r hHr hr
    have hrpos : 0 < r := hs.trans hr.1
    have hur := hu.spatial_smooth hrpos
    have hDu : MemLp (fderiv ℝ (u r)) 2 (volume.restrict unitCube) :=
      critical_continuous_memLp_cube _ (hur.continuous_fderiv (by simp)) 2
    rw [criticalGradientEnergy_sub _ _ hHr.derivative_L2 hDu,
      criticalGradientEnergy_fderiv (u r) hur]
    have hpairs := hHr.weakGradient.inner_laplacian (u r) hur (hu.periodic r hrpos)
    change physicalFieldInner (v r) (laplacian (u r)) =
      -criticalGradientPairing (G r) (fderiv ℝ (u r)) at hpairs
    linarith
  have hDI : IntervalIntegrable
      (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t :=
    ((hDv.add hclassical.1).add (hLap.const_mul 2)).congr_ae hdiff.symm
  have hDint : (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) =
      (∫ r in s..t, criticalGradientEnergy (G r)) +
        (∫ r in s..t, physicalDissipation (u r)) +
          2 * (∫ r in s..t, physicalFieldInner (v r) (laplacian (u r))) := by
    rw [intervalIntegral.integral_congr_ae hdiff]
    rw [intervalIntegral.integral_add (hDv.add hclassical.1) (hLap.const_mul 2),
      intervalIntegral.integral_add hDv hclassical.1, intervalIntegral.integral_const_mul]
  refine ⟨hDI, hN, ?_⟩
  rw [critical_physicalEnergy_sub (v t) (u t) (hv.velocity_L2 t ht.le)
      (critical_continuous_memLp_cube _ (hu.spatial_smooth ht).continuous 2),
    critical_physicalEnergy_sub (v s) (u s) (hv.velocity_L2 s hs.le)
      (critical_continuous_memLp_cube _ (hu.spatial_smooth hs).continuous 2), hDint]
  nlinarith only [henergy, hclassical.2, hcross_eq]

end

end SingularClosure
