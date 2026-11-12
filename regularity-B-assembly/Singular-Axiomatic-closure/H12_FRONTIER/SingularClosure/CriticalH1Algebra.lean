import SingularClosure.CriticalRoughTransport
import SingularClosure.CriticalSmoothCancellation

/-! Physical H1 subtraction and the exact energy polarization identities. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace SingularClosure

noncomputable section

theorem critical_physicalFieldInner_sub_left (v w φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube))
    (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    physicalFieldInner (v - w) φ = physicalFieldInner v φ - physicalFieldInner w φ := by
  unfold physicalFieldInner
  simp_rw [Pi.sub_apply, inner_sub_left]
  exact integral_sub (critical_L2_inner_integrable v φ hv hφ)
    (critical_L2_inner_integrable w φ hw hφ)

theorem critical_physicalEnergy_sub (v w : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube)) :
    physicalEnergy (v - w) = physicalEnergy v + physicalEnergy w - 2 * physicalFieldInner v w := by
  have hv2 : IntegrableOn (fun x => ‖v x‖ ^ 2) unitCube volume := hv.norm.integrable_sq
  have hw2 : IntegrableOn (fun x => ‖w x‖ ^ 2) unitCube volume := hw.norm.integrable_sq
  have hpair := critical_L2_inner_integrable v w hv hw
  have hvdiff : IntegrableOn
      (fun x => ‖v x‖ ^ 2 - 2 * inner ℝ (v x) (w x)) unitCube volume :=
    hv2.sub (hpair.const_mul 2)
  simp_rw [physicalEnergy_eq_integral_norm_sq, Pi.sub_apply, norm_sub_sq_real]
  rw [integral_add hvdiff hw2,
    integral_sub hv2 (hpair.const_mul 2), integral_const_mul]
  unfold physicalFieldInner
  ring

/-- Literal sum of the squared physical weak coordinate derivatives. -/
def criticalGradientEnergy (G : Vec → (Vec →L[ℝ] Vec)) : ℝ :=
  ∑ j : Fin 3, physicalEnergy (fun x => G x (unitVector j))

def criticalGradientPairing (G H : Vec → (Vec →L[ℝ] Vec)) : ℝ :=
  ∑ j : Fin 3, physicalFieldInner (fun x => G x (unitVector j))
    (fun x => H x (unitVector j))

theorem criticalGradientEnergy_nonneg (G : Vec → (Vec →L[ℝ] Vec)) :
    0 ≤ criticalGradientEnergy G := by
  apply Finset.sum_nonneg
  intro j _
  rw [physicalEnergy_eq_integral_norm_sq]
  exact integral_nonneg (fun x => sq_nonneg _)

theorem criticalGradientEnergy_fderiv (u : Field) (hu : ContDiff ℝ ∞ u) :
    criticalGradientEnergy (fderiv ℝ u) = physicalDissipation u := by
  unfold criticalGradientEnergy physicalDissipation
  change (∑ j : Fin 3, physicalEnergy (coordinateDerivative u j)) = _
  exact (integral_gradientSquareDensity_eq_sum_physicalEnergy u hu).symm

theorem criticalGradientEnergy_sub (G H : Vec → (Vec →L[ℝ] Vec))
    (hG : MemLp G 2 (volume.restrict unitCube))
    (hH : MemLp H 2 (volume.restrict unitCube)) :
    criticalGradientEnergy (G - H) = criticalGradientEnergy G + criticalGradientEnergy H -
      2 * criticalGradientPairing G H := by
  have hcolumn (j : Fin 3) :
      (fun x => (G - H) x (unitVector j)) =
        (fun x => G x (unitVector j)) - (fun x => H x (unitVector j)) := rfl
  unfold criticalGradientEnergy criticalGradientPairing
  simp_rw [hcolumn]
  have hterm (j : Fin 3) := critical_physicalEnergy_sub
    (fun x => G x (unitVector j)) (fun x => H x (unitVector j))
    ((ContinuousLinearMap.apply ℝ Vec (unitVector j)).comp_memLp' hG)
    ((ContinuousLinearMap.apply ℝ Vec (unitVector j)).comp_memLp' hH)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Subtracting an actual smooth periodic field preserves the concrete H1 closure. -/
theorem CriticalPhysicalH1.sub_smooth
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)} (hv : CriticalPhysicalH1 v G)
    (u : Field) (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u) :
    CriticalPhysicalH1 (v - u) (G - fderiv ℝ u) := by
  obtain ⟨w, hw, hwp, hvel, hderiv⟩ := hv.approximation
  refine ⟨hv.velocity_L2.sub (critical_continuous_memLp_cube u hu.continuous 2),
    hv.derivative_L2.sub
      (critical_continuous_memLp_cube _ (hu.continuous_fderiv (by simp)) 2), ?_⟩
  refine ⟨fun n => w n - u, (fun n => (hw n).sub hu), ?_, ?_, ?_⟩
  · intro n x i
    change w n (x + unitVector i) - u (x + unitVector i) = w n x - u x
    rw [hwp n, hup]
  · have heq (n : ℕ) : (w n - u) - (v - u) = w n - v := by
      funext x
      change (w n x - u x) - (v x - u x) = w n x - v x
      abel
    simpa only [heq] using hvel
  · have hd (n : ℕ) : fderiv ℝ (w n - u) = fderiv ℝ (w n) - fderiv ℝ u := by
      funext x
      exact (((hw n).differentiable (by simp) x).hasFDerivAt.sub
        ((hu.differentiable (by simp) x).hasFDerivAt)).fderiv
    have heq (n : ℕ) :
        fderiv ℝ (w n - u) - (G - fderiv ℝ u) = fderiv ℝ (w n) - G := by
      rw [hd]
      abel
    simpa only [heq] using hderiv

/-- Weak incompressibility is preserved by subtracting a smooth solenoidal field. -/
theorem critical_gradient_annihilation_sub_smooth
    (v u : Field) (hv : MemLp v 2 (volume.restrict unitCube))
    (hdiv : ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner v (gradient f) = 0)
    (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u)
    (hsol : ∀ x : Vec, divergence u x = 0) :
    ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner (v - u) (gradient f) = 0 := by
  intro f hf hfp
  rw [critical_physicalFieldInner_sub_left v u (gradient f) hv
    (critical_continuous_memLp_cube u hu.continuous 2)
    (critical_continuous_memLp_cube _ (criticalWeak_gradient_continuous f hf) 2),
    hdiv f hf hfp]
  have hz : physicalFieldInner u (gradient f) = 0 :=
    critical_smooth_integral_inner_gradient_eq_zero u f hu hf hup hfp hsol
  rw [hz, sub_self]

end

end SingularClosure
