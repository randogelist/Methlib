import QuasiFeffermanB.EnergyPeriodicRepresentative
import Mathlib.MeasureTheory.Function.Holder

/-! The physical quadratic test pairing is a continuous quadratic form on
actual L2. Multiplication by a bounded matrix field is constructed by the
native Holder operator, with its literal a.e. pointwise meaning. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

abbrev EnergyMatrixLinf := Lp (Vec →L[ℝ] Vec) ∞ (volume.restrict unitCube)

def energyMatrixAction (D : EnergyMatrixLinf) : PhysicalCubeL2 →L[ℝ] PhysicalCubeL2 :=
  (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec)).holderL
    (volume.restrict unitCube) ∞ 2 2 D

theorem energyMatrixAction_coe (D : EnergyMatrixLinf) (v : PhysicalCubeL2) :
    (energyMatrixAction D v : Field) =ᵐ[volume.restrict unitCube]
      (fun x => D x (v x)) :=
  (ContinuousLinearMap.id ℝ (Vec →L[ℝ] Vec)).coeFn_holder D v

def energyTestMatrix (φ : Field) (hφ : ContDiff ℝ ∞ φ) : EnergyMatrixLinf :=
  (critical_continuous_memLp_cube (fderiv ℝ φ) (hφ.continuous_fderiv (by simp)) ∞).toLp
    (fderiv ℝ φ)

theorem energyTestMatrix_coe (φ : Field) (hφ : ContDiff ℝ ∞ φ) :
    (energyTestMatrix φ hφ : Vec → (Vec →L[ℝ] Vec)) =ᵐ[volume.restrict unitCube]
      fderiv ℝ φ :=
  (critical_continuous_memLp_cube (fderiv ℝ φ) (hφ.continuous_fderiv (by simp)) ∞).coeFn_toLp

theorem energyWeakTransport_eq_L2_inner (v φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hφ : ContDiff ℝ ∞ φ) :
    criticalWeakTransport v φ =
      inner ℝ (hv.toLp v) (energyMatrixAction (energyTestMatrix φ hφ) (hv.toLp v)) := by
  rw [L2.inner_def]
  unfold criticalWeakTransport
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp,
    energyMatrixAction_coe (energyTestMatrix φ hφ) (hv.toLp v),
    energyTestMatrix_coe φ hφ] with x hx hy hz
  rw [hy, hz, hx]

theorem energyMatrixQuadratic_continuous (D : EnergyMatrixLinf) :
    Continuous (fun v : PhysicalCubeL2 => inner ℝ v (energyMatrixAction D v)) :=
  continuous_id.inner (energyMatrixAction D).continuous

theorem energyWeakTransport_L2_tendsto
    {ι : Type*} {l : Filter ι} (v : ι → PhysicalCubeL2) (w : PhysicalCubeL2)
    (hvw : Tendsto v l (𝓝 w)) (φ : Field) (hφ : ContDiff ℝ ∞ φ) :
    Tendsto (fun n => criticalWeakTransport (v n : Field) φ) l
      (𝓝 (criticalWeakTransport (w : Field) φ)) := by
  have h := (energyMatrixQuadratic_continuous (energyTestMatrix φ hφ)).continuousAt.tendsto.comp hvw
  simpa only [energyWeakTransport_eq_L2_inner _ φ (Lp.memLp _) hφ, Lp.toLp_coeFn]
    using h

theorem energyMatrixQuadratic_bound (D : EnergyMatrixLinf) (v : PhysicalCubeL2) :
    |inner ℝ v (energyMatrixAction D v)| ≤ ‖energyMatrixAction D‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖energyMatrixAction D v‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v (energyMatrixAction D v)
    _ ≤ ‖v‖ * (‖energyMatrixAction D‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((energyMatrixAction D).le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

theorem energyWeakTransport_L2_bound (v φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hφ : ContDiff ℝ ∞ φ) :
    |criticalWeakTransport v φ| ≤
      ‖energyMatrixAction (energyTestMatrix φ hφ)‖ * ‖hv.toLp v‖ ^ 2 := by
  rw [energyWeakTransport_eq_L2_inner v φ hv hφ]
  exact energyMatrixQuadratic_bound _ _

theorem energyWeakTransport_congr_ae {v w φ : Field}
    (heq : v =ᵐ[volume.restrict unitCube] w) :
    criticalWeakTransport v φ = criticalWeakTransport w φ := by
  unfold criticalWeakTransport
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

end
end QuasiFeffermanB
