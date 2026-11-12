import QuasiFeffermanB.EnergyWeakContinuity
import QuasiFeffermanB.EnergyPeriodicRepresentative
import QuasiFeffermanB.LHRestart
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual physical L2 weak continuity through the real adjoint of the
Fourier realization and the exact periodic representative. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped Topology
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

local instance : InnerProductSpace ℝ (TorusSobolev 0) :=
  InnerProductSpace.rclikeToReal ℂ (TorusSobolev 0)

def energyH0PhysicalMap : TorusSobolev 0 →L[ℝ] PhysicalCubeL2 :=
  torusToPhysicalCubeL2.comp (torusSobolevL2.toContinuousLinearMap.restrictScalars ℝ)

theorem energyH0PhysicalMap_apply (U : ℝ → TorusSobolev 0) (t : ℝ) :
    energyH0PhysicalMap (U t) = energyPhysicalVelocityL2 U t := rfl

theorem ENERGY_PHYSICAL_L2_WEAK_CONTINUITY
    (U : ℝ → TorusSobolev 0) (I : Set ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ I, ‖U t‖ ≤ R)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) I)
    (φ : PhysicalCubeL2) :
    ContinuousOn (fun t => inner ℝ (energyPhysicalVelocityL2 U t) φ) I := by
  have hc := ENERGY_H0_WEAK_CONTINUITY U I R hR hbound hcoord
    (energyH0PhysicalMap.adjoint φ)
  have hr : ContinuousOn
      (fun t => inner ℝ (U t) (energyH0PhysicalMap.adjoint φ)) I := by
    change ContinuousOn
      (fun t => Complex.re (inner ℂ (U t) (energyH0PhysicalMap.adjoint φ))) I
    exact Complex.continuous_re.comp_continuousOn hc
  simpa only [ContinuousLinearMap.adjoint_inner_right, energyH0PhysicalMap_apply] using hr

theorem ENERGY_PERIODIC_WEAK_CONTINUITY
    (U : ℝ → TorusSobolev 0) (I : Set ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ I, ‖U t‖ ≤ R)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) I)
    (φ : Field) (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    ContinuousOn (fun t => physicalFieldInner (energyPeriodicVelocity U t) φ) I := by
  have h := ENERGY_PHYSICAL_L2_WEAK_CONTINUITY U I R hR hbound hcoord
    (criticalL2Representative φ)
  have heq : (fun t => inner ℝ (energyPhysicalVelocityL2 U t) (criticalL2Representative φ)) =
      (fun t => physicalFieldInner (energyPeriodicVelocity U t) φ) := by
    funext t
    rw [← energyPeriodicVelocity_L2 U t]
    exact restart_representative_inner _ _ (energyPeriodicVelocity_memLp U t) hφ
  rwa [heq] at h

end
end QuasiFeffermanB
