import SingularClosure.CriticalRoughHolder

/-! Real-valued critical transport estimate with a universal physical H1 constant. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SingularClosure
noncomputable section

/-- Actual physical Lp norm, used only together with proved finite Lp membership. -/
def criticalSpatialNorm {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (v : Vec → E) : ℝ :=
  (eLpNorm v p (volume.restrict unitCube)).toReal

theorem criticalSpatialNorm_nonneg {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (v : Vec → E) : 0 ≤ criticalSpatialNorm p v := ENNReal.toReal_nonneg

theorem CRITICAL_PHYSICAL_H1_L6_REAL :
    ∃ L : ℝ, 0 < L ∧ ∀ (v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      CriticalPhysicalH1 v G →
      criticalSpatialNorm 6 v ≤ L * (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v) := by
  obtain ⟨K, hK0, hK⟩ := CRITICAL_PHYSICAL_H1_L6
  let C : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ)
  have hC : C < ⊤ := by dsimp [C]; finiteness
  refine ⟨C.toReal * (1 + K) + 1, by positivity, ?_⟩
  intro v G hv
  have hbound := hK v G hv
  change eLpNorm v 6 (volume.restrict unitCube) ≤ C *
    (eLpNorm G 2 (volume.restrict unitCube) +
      ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)) at hbound
  have hG := hv.derivative_L2.eLpNorm_lt_top
  have hV := hv.velocity_L2.eLpNorm_lt_top
  have hKV : ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube) ≠ ⊤ := by
    finiteness
  have hfinite : C * (eLpNorm G 2 (volume.restrict unitCube) +
      ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)) ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hG.ne hKV,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0] at hr
  change criticalSpatialNorm 6 v ≤ C.toReal *
    (criticalSpatialNorm 2 G + K * criticalSpatialNorm 2 v) at hr
  have hD := criticalSpatialNorm_nonneg 2 G
  have hW := criticalSpatialNorm_nonneg 2 v
  calc
    _ ≤ _ := hr
    _ ≤ C.toReal * ((1 + K) * (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v)) := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      nlinarith [mul_nonneg hK0 hD]
    _ ≤ _ := by nlinarith

/-- A single universal constant controls the full physical rough transport. -/
theorem CRITICAL_ROUGH_TRANSPORT_INTERPOLATED :
    ∃ A : ℝ, 0 < A ∧ ∀ (u v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      MemLp u 6 (volume.restrict unitCube) → CriticalPhysicalH1 v G →
      abs (criticalRoughTransport v G u) ≤
        A * criticalSpatialNorm 6 u * Real.sqrt (criticalSpatialNorm 2 v) *
          Real.sqrt (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v) *
            criticalSpatialNorm 2 G := by
  obtain ⟨L, hL, hSob⟩ := CRITICAL_PHYSICAL_H1_L6_REAL
  refine ⟨Real.sqrt L, Real.sqrt_pos.2 hL, ?_⟩
  intro u v G hu hv
  have hv3 := hv.memLp_three
  have hv6 := hv.memLp_six
  have hG := hv.derivative_L2
  have hW := hv.velocity_L2
  have hb := (CRITICAL_ROUGH_TRANSPORT_HOLDER u v G hu hv3 hG).2
  have hfin : (eLpNorm u 6 (volume.restrict unitCube) *
      eLpNorm v 3 (volume.restrict unitCube)) *
      eLpNorm G 2 (volume.restrict unitCube) ≠ ⊤ := by
    finiteness [hu.2, hv3.2, hG.2]
  have hbR := ENNReal.toReal_mono hfin hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hbR
  change abs (criticalRoughTransport v G u) ≤
    (criticalSpatialNorm 6 u * criticalSpatialNorm 3 v) * criticalSpatialNorm 2 G at hbR
  have hi := critical_eLpNorm_three_le_interpolation v hW.1
  have hiFin : eLpNorm v 2 (volume.restrict unitCube) ^ (1 / 2 : ℝ) *
      eLpNorm v 6 (volume.restrict unitCube) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness [hW.2, hv6.2]
  have hiR := ENNReal.toReal_mono hiFin hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] at hiR
  change criticalSpatialNorm 3 v ≤
    Real.sqrt (criticalSpatialNorm 2 v) * Real.sqrt (criticalSpatialNorm 6 v) at hiR
  have hs : Real.sqrt (criticalSpatialNorm 6 v) ≤
      Real.sqrt L * Real.sqrt (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v) := by
    rw [← Real.sqrt_mul hL.le]
    exact Real.sqrt_le_sqrt (hSob v G hv)
  have hU0 := criticalSpatialNorm_nonneg 6 u
  have hD0 := criticalSpatialNorm_nonneg 2 G
  calc
    _ ≤ _ := hbR
    _ ≤ (criticalSpatialNorm 6 u *
        (Real.sqrt (criticalSpatialNorm 2 v) * Real.sqrt (criticalSpatialNorm 6 v))) *
          criticalSpatialNorm 2 G :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hiR hU0) hD0
    _ ≤ (criticalSpatialNorm 6 u *
        (Real.sqrt (criticalSpatialNorm 2 v) *
          (Real.sqrt L * Real.sqrt (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v)))) *
            criticalSpatialNorm 2 G :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) hU0) hD0
    _ = _ := by ring

end
end SingularClosure
