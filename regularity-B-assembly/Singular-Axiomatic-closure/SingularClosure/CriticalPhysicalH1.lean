import SingularClosure.CriticalWeakGradient
import SingularClosure.PeriodicSobolev
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Concrete periodic H1 as the closure of smooth periodic fields in the
physical velocity/derivative L2 norm. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace SingularClosure
noncomputable section

structure CriticalPhysicalH1 (v : Field) (G : Vec → (Vec →L[ℝ] Vec)) : Prop where
  velocity_L2 : MemLp v 2 (volume.restrict unitCube)
  derivative_L2 : MemLp G 2 (volume.restrict unitCube)
  approximation : ∃ w : ℕ → Field,
    (∀ n, ContDiff ℝ ∞ (w n)) ∧ (∀ n, SpatialPeriodic (w n)) ∧
    Tendsto (fun n => eLpNorm (w n - v) 2 (volume.restrict unitCube)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fderiv ℝ (w n) - G) 2 (volume.restrict unitCube)) atTop (𝓝 0)

theorem CriticalPhysicalH1.weakGradient
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)} (h : CriticalPhysicalH1 v G) :
    CriticalWeakGradient v G := by
  obtain ⟨w, hw, hwp, hv, hG⟩ := h.approximation
  exact CRITICAL_WEAK_GRADIENT_OF_SMOOTH_APPROXIMATION v G w
    h.velocity_L2 h.derivative_L2 hw hwp hv hG


/-- Physical L2 convergence implies convergence of the actual extended L2 norms. -/
theorem critical_eLpNorm_two_tendsto
    {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Vec → E) (g : Vec → E)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict unitCube))
      atTop (𝓝 (eLpNorm g 2 (volume.restrict unitCube))) := by
  have h := (critical_toLp_tendsto_of_eLpNorm_sub f g hf hg hconv).enorm
  simpa only [Lp.enorm_toLp] using h

/-- Variable bounds pass to a limit in measure by actual Lp lower semicontinuity. -/
theorem critical_eLpNorm_le_of_convergent_bound
    {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Vec → E) (g : Vec → E) (p : ℝ≥0∞)
    (b : ℕ → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict unitCube))
    (hmeasure : TendstoInMeasure (volume.restrict unitCube) f atTop g)
    (hb : ∀ n, eLpNorm (f n) p (volume.restrict unitCube) ≤ b n)
    (hB : Tendsto b atTop (𝓝 B)) :
    eLpNorm g p (volume.restrict unitCube) ≤ B := by
  by_contra hn
  obtain ⟨d, hBd, hd⟩ := exists_between (lt_of_not_ge hn)
  have hbound : ∀ᶠ n in atTop, eLpNorm (f n) p (volume.restrict unitCube) ≤ d := by
    filter_upwards [hB.eventually (gt_mem_nhds hBd)] with n hn
    exact (hb n).trans hn.le
  exact (not_le_of_gt hd) (eLpNorm_le_of_tendstoInMeasure hbound hmeasure hf)

/-- The actual periodic H1-to-L6 inequality extends to the full H1 closure. -/
theorem CRITICAL_PHYSICAL_H1_L6 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      CriticalPhysicalH1 v G →
      eLpNorm v 6 (volume.restrict unitCube) ≤
        (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
          (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (eLpNorm G 2 (volume.restrict unitCube) +
            ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)) := by
  obtain ⟨K, hK0, hK⟩ := PERIODIC_SOBOLEV_H1_L6 (F := Vec)
  refine ⟨K, hK0, ?_⟩
  intro v G hv
  obtain ⟨w, hw, hwp, hvelocity, hderivative⟩ := hv.approximation
  have hw2 (n : ℕ) : MemLp (w n) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube (w n) (hw n).continuous 2
  have hD2 (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ ((hw n).continuous_fderiv (by simp)) 2
  have hV := critical_eLpNorm_two_tendsto w v hw2 hv.velocity_L2 hvelocity
  have hD := critical_eLpNorm_two_tendsto (fun n => fderiv ℝ (w n)) G
    hD2 hv.derivative_L2 hderivative
  let C : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ)
  have hC : C < ⊤ := by dsimp [C]; finiteness
  have hKV := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hV
    (Or.inr ENNReal.ofReal_ne_top)
  have hB := ENNReal.Tendsto.const_mul (a := C) (hD.add hKV) (Or.inr hC.ne)
  apply critical_eLpNorm_le_of_convergent_bound w v 6
    (fun n => C * (eLpNorm (fderiv ℝ (w n)) 2 (volume.restrict unitCube) +
      ENNReal.ofReal K * eLpNorm (w n) 2 (volume.restrict unitCube)))
    (C * (eLpNorm G 2 (volume.restrict unitCube) +
      ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)))
    (fun n => (hw2 n).aestronglyMeasurable)
  · exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n => (hw2 n).aestronglyMeasurable) hv.velocity_L2.aestronglyMeasurable hvelocity
  · intro n
    exact hK (w n) (hw n) (hwp n)
  · exact hB

theorem CriticalPhysicalH1.memLp_six
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)} (h : CriticalPhysicalH1 v G) :
    MemLp v 6 (volume.restrict unitCube) := by
  obtain ⟨K, _hK, hb⟩ := CRITICAL_PHYSICAL_H1_L6
  refine ⟨h.velocity_L2.aestronglyMeasurable, (hb v G h).trans_lt ?_⟩
  have hv := h.velocity_L2.eLpNorm_lt_top
  have hG := h.derivative_L2.eLpNorm_lt_top
  finiteness

end
end SingularClosure
