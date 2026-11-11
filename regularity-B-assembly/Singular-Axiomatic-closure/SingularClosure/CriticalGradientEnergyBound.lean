import SingularClosure.CriticalH1Algebra
import SingularClosure.PeriodicSobolev
import SingularClosure.CriticalYoung
import SingularClosure.CriticalSerrinEstimate
import Mathlib.MeasureTheory.Function.L2Space

/-! The rough operator L2 norm is controlled by the literal physical gradient energy. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

theorem critical_eLpNorm_two_toReal_sq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Vec} (f : Vec → F) (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [eLpNorm_two_eq_integral_norm_sq_rpow f μ hf.norm.integrable_sq,
    ENNReal.toReal_rpow, ENNReal.toReal_ofReal hnonneg,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]

/-- The real L2 norm square is exactly the literal physical kinetic energy. -/
theorem critical_velocity_L2_toReal_sq_eq_physicalEnergy
    (v : Field) (hv : MemLp v 2 (volume.restrict unitCube)) :
    (eLpNorm v 2 (volume.restrict unitCube)).toReal ^ 2 = physicalEnergy v := by
  rw [physicalEnergy_eq_integral_norm_sq]
  exact critical_eLpNorm_two_toReal_sq v hv

/-- No smoothness is used in the operator-to-coordinate gradient estimate. -/
theorem critical_gradient_L2_toReal_sq_le
    (G : Vec → (Vec →L[ℝ] Vec)) (hG : MemLp G 2 (volume.restrict unitCube)) :
    (eLpNorm G 2 (volume.restrict unitCube)).toReal ^ 2 ≤ 3 * criticalGradientEnergy G := by
  have hcolumn (j : Fin 3) : MemLp (fun x => G x (unitVector j)) 2
      (volume.restrict unitCube) :=
    (ContinuousLinearMap.apply ℝ Vec (unitVector j)).comp_memLp' hG
  have hcolumnSq (j : Fin 3) : IntegrableOn (fun x => ‖G x (unitVector j)‖ ^ 2)
      unitCube volume := (hcolumn j).norm.integrable_sq
  calc
    _ = ∫ x in unitCube, ‖G x‖ ^ 2 := critical_eLpNorm_two_toReal_sq G hG
    _ ≤ ∫ x in unitCube, 3 * ∑ j : Fin 3, ‖G x (unitVector j)‖ ^ 2 :=
      integral_mono hG.norm.integrable_sq
        ((integrable_finset_sum _ (fun j _ => hcolumnSq j)).const_mul 3)
        (fun x => opNorm_sq_le_three_sum_coordinate_sq (G x))
    _ = 3 * criticalGradientEnergy G := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hcolumnSq j)]
      simp only [criticalGradientEnergy, physicalEnergy_eq_integral_norm_sq]

/-- Scalar Young with ν/3 absorbs the operator norm into physical coordinate energy. -/
theorem critical_transport_young_of_energy_bounds
    (ν C U W D E Q : ℝ) (hν : 0 < ν) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hD : 0 ≤ D) (hWE : W ^ 2 = E) (hDQ : D ^ 2 ≤ 3 * Q) :
    C * U * Real.sqrt W * Real.sqrt (D + W) * D ≤
      (ν / 2) * Q + (216 * C ^ 4 * U ^ 4 / ν ^ 3 + 3 * C ^ 2 * U ^ 2 / ν) * E := by
  have h := CRITICAL_TRANSPORT_YOUNG (ν / 3) C U W D (by positivity) hC hU hW hD
  have hcoef : 8 * C ^ 4 * U ^ 4 / (ν / 3) ^ 3 + C ^ 2 * U ^ 2 / (ν / 3) =
      216 * C ^ 4 * U ^ 4 / ν ^ 3 + 3 * C ^ 2 * U ^ 2 / ν := by
    field_simp [hν.ne'] <;> ring
  rw [hcoef, hWE] at h
  apply h.trans
  calc
    _ ≤ ((ν / 3) / 2) * (3 * Q) +
        (216 * C ^ 4 * U ^ 4 / ν ^ 3 + 3 * C ^ 2 * U ^ 2 / ν) * E := by
      exact add_le_add (mul_le_mul_of_nonneg_left hDQ (by positivity)) le_rfl
    _ = _ := by ring

/-- The literal rough L2 quantities satisfy the physical Young estimate. -/
theorem CRITICAL_TRANSPORT_YOUNG_PHYSICAL_ENERGY
    (ν C U : ℝ) (hν : 0 < ν) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hG : MemLp G 2 (volume.restrict unitCube)) :
    C * U * Real.sqrt ((eLpNorm v 2 (volume.restrict unitCube)).toReal) *
        Real.sqrt ((eLpNorm G 2 (volume.restrict unitCube)).toReal +
          (eLpNorm v 2 (volume.restrict unitCube)).toReal) *
        (eLpNorm G 2 (volume.restrict unitCube)).toReal ≤
      (ν / 2) * criticalGradientEnergy G +
        (216 * C ^ 4 * U ^ 4 / ν ^ 3 + 3 * C ^ 2 * U ^ 2 / ν) * physicalEnergy v := by
  exact critical_transport_young_of_energy_bounds ν C U
    (eLpNorm v 2 (volume.restrict unitCube)).toReal
    (eLpNorm G 2 (volume.restrict unitCube)).toReal
    (physicalEnergy v) (criticalGradientEnergy G) hν hC hU
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (critical_velocity_L2_toReal_sq_eq_physicalEnergy v hv)
    (critical_gradient_L2_toReal_sq_le G hG)

/-- The actual rough transport is absorbed by physical gradient energy. -/
theorem CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : ℝ), 0 < ν →
      ∀ (u v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      MemLp u 6 (volume.restrict unitCube) → CriticalPhysicalH1 v G →
      abs (criticalRoughTransport v G u) ≤
        (ν / 2) * criticalGradientEnergy G +
          (216 * C ^ 4 * (criticalSpatialNorm 6 u) ^ 4 / ν ^ 3 +
            3 * C ^ 2 * (criticalSpatialNorm 6 u) ^ 2 / ν) * physicalEnergy v := by
  obtain ⟨C, hC, htransport⟩ := CRITICAL_ROUGH_TRANSPORT_INTERPOLATED
  refine ⟨C, hC, ?_⟩
  intro ν hν u v G hu hv
  apply (htransport u v G hu hv).trans
  exact CRITICAL_TRANSPORT_YOUNG_PHYSICAL_ENERGY ν C (criticalSpatialNorm 6 u)
    hν hC.le (criticalSpatialNorm_nonneg 6 u) v G hv.velocity_L2 hv.derivative_L2

/-- The U^4 and U^2 coefficient is time-integrable under the actual Serrin L4 bound. -/
theorem criticalSerrinEnergyCoefficient_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (ν C : ℝ) (U : α → ℝ) (hU : MemLp U 4 μ) :
    Integrable (fun t => 216 * C ^ 4 * (U t) ^ 4 / ν ^ 3 +
      3 * C ^ 2 * (U t) ^ 2 / ν) μ := by
  have h4 : Integrable (fun t => (U t) ^ 4) μ := by
    have h := hU.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h
  have h2 : Integrable (fun t => (U t) ^ 2) μ :=
    (hU.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq
  apply ((h4.const_mul (216 * C ^ 4 / ν ^ 3)).add
    (h2.const_mul (3 * C ^ 2 / ν))).congr
  exact Filter.Eventually.of_forall fun t => by
    change (216 * C ^ 4 / ν ^ 3) * (U t) ^ 4 + (3 * C ^ 2 / ν) * (U t) ^ 2 = _
    ring

end

end SingularClosure
