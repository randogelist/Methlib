import SingularClosure.CriticalPhysicalH1
import SingularClosure.CriticalRoughTransport
import SingularClosure.PeriodicNonlinear

/-! Actual rough trilinear bounds for weak-strong uniqueness. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators ContDiff ENNReal Topology
namespace SingularClosure
noncomputable section
variable {F : Type*} [NormedAddCommGroup F]

theorem critical_eLpNorm_three_le_interpolation (v : Vec → F) (hv : AEStronglyMeasurable v (volume.restrict unitCube)) :
    eLpNorm v 3 (volume.restrict unitCube) ≤
      eLpNorm v 2 (volume.restrict unitCube) ^ (1 / 2 : ℝ) *
        eLpNorm v 6 (volume.restrict unitCube) ^ (1 / 2 : ℝ) := by
  letI : ENNReal.HolderTriple 4 12 3 := by
    have h : Real.HolderTriple (4 : ℝ) 12 3 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hc : AEStronglyMeasurable (fun x => ‖v x‖ ^ (1 / 2 : ℝ))
      (volume.restrict unitCube) :=
    (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable hv.norm
  have hprod : (fun x => ‖v x‖ ^ (1 / 2 : ℝ) * ‖v x‖ ^ (1 / 2 : ℝ)) =
      (fun x => ‖v x‖) := by
    funext x
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
    norm_num
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 4) (q := 12) (r := 3)
    hc hc
    (fun a b : ℝ => a * b) 1
    (Filter.Eventually.of_forall (fun x => by
      simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  rw [hprod, eLpNorm_norm,
    eLpNorm_norm_rpow v (by norm_num), eLpNorm_norm_rpow v (by norm_num)] at h
  have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 2 := by
    calc
      _ = ENNReal.ofReal ((4 : ℝ) * (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 2 := by norm_num
  have h12 : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 6 := by
    calc
      _ = ENNReal.ofReal ((12 : ℝ) * (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 6 := by norm_num
  simpa only [h4, h12, ENNReal.coe_one, one_mul] using h



theorem criticalRoughTransport_aestronglyMeasurable
    (u v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (hu : AEStronglyMeasurable u (volume.restrict unitCube))
    (hv : AEStronglyMeasurable v (volume.restrict unitCube))
    (hG : AEStronglyMeasurable G (volume.restrict unitCube)) :
    AEStronglyMeasurable (fun x => inner ℝ (u x) (G x (v x)))
      (volume.restrict unitCube) := by
  have he : Continuous (fun z : (Vec →L[ℝ] Vec) × Vec => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hu.inner (he.comp_aestronglyMeasurable (hG.prodMk hv))

/-- Hölder exponents 6,3,2 for the literal rough transport integral. -/
theorem criticalRoughTransport_eLpNorm_one_le
    (u v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (hu : AEStronglyMeasurable u (volume.restrict unitCube))
    (hv : AEStronglyMeasurable v (volume.restrict unitCube))
    (hG : AEStronglyMeasurable G (volume.restrict unitCube)) :
    eLpNorm (fun x => inner ℝ (u x) (G x (v x))) 1 (volume.restrict unitCube) ≤
      (eLpNorm u 6 (volume.restrict unitCube) *
        eLpNorm v 3 (volume.restrict unitCube)) *
          eLpNorm G 2 (volume.restrict unitCube) := by
  letI : ENNReal.HolderTriple 6 3 2 := by
    have h : Real.HolderTriple (6 : ℝ) 3 2 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hprod := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 6) (q := 3) (r := 2)
    hu.norm hv.norm (fun x y : ℝ => x * y) 1
    (Filter.Eventually.of_forall (fun x => by simp only [norm_mul, NNReal.coe_one, one_mul]))
  simp only [ENNReal.coe_one, one_mul, eLpNorm_norm] at hprod
  have htriple := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 2) (q := 2) (r := 1)
    (hu.norm.mul hv.norm) hG.norm (fun x y : ℝ => x * y) 1
    (Filter.Eventually.of_forall (fun x => by simp only [norm_mul, NNReal.coe_one, one_mul]))
  simp only [ENNReal.coe_one, one_mul, eLpNorm_norm] at htriple
  calc
    _ ≤ eLpNorm (fun x => (‖u x‖ * ‖v x‖) * ‖G x‖) 1
        (volume.restrict unitCube) := by
      apply eLpNorm_mono_real
      intro x
      calc
        _ ≤ ‖u x‖ * ‖G x (v x)‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ ‖u x‖ * (‖G x‖ * ‖v x‖) :=
          mul_le_mul_of_nonneg_left ((G x).le_opNorm (v x)) (norm_nonneg _)
        _ = _ := by ring
    _ ≤ _ := htriple.trans (mul_le_mul_of_nonneg_right hprod bot_le)

theorem CRITICAL_ROUGH_TRANSPORT_HOLDER
    (u v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (hu : MemLp u 6 (volume.restrict unitCube))
    (hv : MemLp v 3 (volume.restrict unitCube))
    (hG : MemLp G 2 (volume.restrict unitCube)) :
    IntegrableOn (fun x => inner ℝ (u x) (G x (v x))) unitCube volume ∧
    ENNReal.ofReal (abs (criticalRoughTransport v G u)) ≤
      (eLpNorm u 6 (volume.restrict unitCube) *
        eLpNorm v 3 (volume.restrict unitCube)) *
          eLpNorm G 2 (volume.restrict unitCube) := by
  have hbound := criticalRoughTransport_eLpNorm_one_le u v G hu.1 hv.1 hG.1
  have hmem : MemLp (fun x => inner ℝ (u x) (G x (v x))) 1
      (volume.restrict unitCube) := by
    refine ⟨criticalRoughTransport_aestronglyMeasurable u v G hu.1 hv.1 hG.1,
      hbound.trans_lt ?_⟩
    finiteness [hu.2, hv.2, hG.2]
  refine ⟨hmem.integrable (by norm_num), ?_⟩
  calc
    _ = ‖(∫ x in unitCube, inner ℝ (u x) (G x (v x)))‖ₑ := by
      rw [← ofReal_norm, Real.norm_eq_abs]
      rfl
    _ ≤ ∫⁻ x, ‖inner ℝ (u x) (G x (v x))‖ₑ ∂volume.restrict unitCube :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => inner ℝ (u x) (G x (v x))) 1
        (volume.restrict unitCube) :=
      (eLpNorm_one_eq_lintegral_enorm (f := fun x => inner ℝ (u x) (G x (v x)))).symm
    _ ≤ _ := hbound

theorem CriticalPhysicalH1.memLp_three
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)} (h : CriticalPhysicalH1 v G) :
    MemLp v 3 (volume.restrict unitCube) := by
  have h6 := h.memLp_six
  have hb := critical_eLpNorm_three_le_interpolation v h.velocity_L2.aestronglyMeasurable
  refine ⟨h.velocity_L2.aestronglyMeasurable, hb.trans_lt ?_⟩
  finiteness [h.velocity_L2.2, h6.2]

end
end SingularClosure
