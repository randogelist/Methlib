import SingularClosure.CriticalWeakMomentum
import SingularClosure.CriticalPeriodicIBP

/-!
Physical weak gradients obtained from actual smooth H1 approximation.
The approximation hypotheses are convergence in velocity L2 and derivative L2;
no integration-by-parts, cross-energy, or uniqueness conclusion is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace SingularClosure

noncomputable section

/-- The actual distributional first derivative on the periodic cube. -/
structure CriticalWeakGradient (v : Field) (G : Vec → (Vec →L[ℝ] Vec)) : Prop where
  velocity_L2 : MemLp v 2 (volume.restrict unitCube)
  derivative_L2 : MemLp G 2 (volume.restrict unitCube)
  integration_by_parts : ∀ φ : Field, ContDiff ℝ ∞ φ → SpatialPeriodic φ → ∀ j : Fin 3,
    physicalFieldInner v (coordinateDerivative φ j) =
      -physicalFieldInner (fun x => G x (unitVector j)) φ

theorem critical_continuous_memLp_cube {E : Type*} [NormedAddCommGroup E]
    (f : Vec → E) (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict unitCube) := by
  haveI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_unitCube.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := isCompact_unitCube.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
  exact hC x hx

/-- Genuine L2 convergence of function representatives gives norm convergence
of their physical L2 equivalence classes. -/
theorem critical_toLp_tendsto_of_eLpNorm_sub
    {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → Vec → E) (g : Vec → E)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd (n : ℕ) : dist ((hf n).toLp (f n)) (hg.toLp g) =
      (eLpNorm (f n - g) 2 (volume.restrict unitCube)).toReal := by
    rw [dist_eq_norm, ← (hf n).toLp_sub hg, Lp.norm_toLp]
  simp_rw [hd]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hconv

theorem critical_physicalFieldInner_eq_L2_inner
    (v φ : Field) (hv : MemLp v 2 (volume.restrict unitCube))
    (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    physicalFieldInner v φ = inner ℝ (hv.toLp v) (hφ.toLp φ) := by
  rw [L2.inner_def]
  unfold physicalFieldInner
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp, hφ.coeFn_toLp] with x hx hφx
  rw [hx, hφx]

theorem critical_toLp_compCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Vec) (f : Vec → E)
    (hf : MemLp f 2 (volume.restrict unitCube)) :
    (L.comp_memLp' hf).toLp (L ∘ f) =
      L.compLpL 2 (volume.restrict unitCube) (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [(L.comp_memLp' hf).coeFn_toLp,
    L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp] with x hleft hright hfval
  rw [hleft, hright, hfval]
  rfl

/-- Passing a smooth test pairing to the physical L2 limit. -/
theorem critical_physicalFieldInner_tendsto
    (f : ℕ → Field) (g φ : Field)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube))
    (hφ : MemLp φ 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => physicalFieldInner (f n) φ) atTop (𝓝 (physicalFieldInner g φ)) := by
  have hLp := critical_toLp_tendsto_of_eLpNorm_sub f g hf hg hconv
  have hi : Tendsto (fun n => inner ℝ ((hf n).toLp (f n)) (hφ.toLp φ))
      atTop (𝓝 (inner ℝ (hg.toLp g) (hφ.toLp φ))) := hLp.inner tendsto_const_nhds
  simpa only [← critical_physicalFieldInner_eq_L2_inner] using hi

/-- The same limit passage after applying a concrete continuous linear map.
In particular it applies to each column of the actual weak derivative. -/
theorem critical_physicalFieldInner_compCLM_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Vec) (f : ℕ → Vec → E) (g : Vec → E) (φ : Field)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube))
    (hφ : MemLp φ 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => physicalFieldInner (L ∘ f n) φ)
      atTop (𝓝 (physicalFieldInner (L ∘ g) φ)) := by
  have hLp := critical_toLp_tendsto_of_eLpNorm_sub f g hf hg hconv
  have hL := ((L.compLpL 2 (volume.restrict unitCube)).continuous.tendsto (hg.toLp g)).comp hLp
  have hi : Tendsto
      (fun n => inner ℝ (L.compLpL 2 (volume.restrict unitCube) ((hf n).toLp (f n))) (hφ.toLp φ))
      atTop (𝓝 (inner ℝ (L.compLpL 2 (volume.restrict unitCube) (hg.toLp g)) (hφ.toLp φ))) :=
    hL.inner tendsto_const_nhds
  have hpair (w : Vec → E) (hw : MemLp w 2 (volume.restrict unitCube)) :
      physicalFieldInner (L ∘ w) φ =
        inner ℝ (L.compLpL 2 (volume.restrict unitCube) (hw.toLp w)) (hφ.toLp φ) := by
    rw [critical_physicalFieldInner_eq_L2_inner (L ∘ w) φ (L.comp_memLp' hw) hφ,
      critical_toLp_compCLM L w hw]
  simpa only [← hpair] using hi

/-- The H1 closure definition yields the actual distributional gradient. -/
theorem CRITICAL_WEAK_GRADIENT_OF_SMOOTH_APPROXIMATION
    (v : Field) (G : Vec → (Vec →L[ℝ] Vec)) (w : ℕ → Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hG : MemLp G 2 (volume.restrict unitCube))
    (hw : ∀ n, ContDiff ℝ ∞ (w n)) (hwp : ∀ n, SpatialPeriodic (w n))
    (hvelocity : Tendsto (fun n => eLpNorm (w n - v) 2 (volume.restrict unitCube))
      atTop (𝓝 0))
    (hderivative : Tendsto
      (fun n => eLpNorm (fderiv ℝ (w n) - G) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    CriticalWeakGradient v G := by
  refine ⟨hv, hG, ?_⟩
  intro φ hφ hφp j
  have hwL2 (n : ℕ) : MemLp (w n) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (hw n).continuous 2
  have hwDL2 (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ ((hw n).continuous_fderiv (by simp)) 2
  have hφL2 : MemLp φ 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube φ hφ.continuous 2
  have hφDL2 : MemLp (coordinateDerivative φ j) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (coordinateDerivative_continuous hφ j) 2
  have hleft := critical_physicalFieldInner_tendsto w v (coordinateDerivative φ j)
    hwL2 hv hφDL2 hvelocity
  have hright : Tendsto
      (fun n => physicalFieldInner (coordinateDerivative (w n) j) φ)
      atTop (𝓝 (physicalFieldInner (fun x => G x (unitVector j)) φ)) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, coordinateDerivative] using
      critical_physicalFieldInner_compCLM_tendsto
        (ContinuousLinearMap.apply ℝ Vec (unitVector j))
        (fun n => fderiv ℝ (w n)) G φ hwDL2 hG hφL2 hderivative
  have heq : (fun n => physicalFieldInner (w n) (coordinateDerivative φ j)) =
      (fun n => -physicalFieldInner (coordinateDerivative (w n) j) φ) := by
    funext n
    exact critical_integral_inner_coordinateDerivative (w n) φ (hw n) hφ (hwp n) hφp j
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright.neg

/-- Rough diffusion pairing, proved from distributional first derivatives. -/
theorem CriticalWeakGradient.inner_laplacian
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)} (hv : CriticalWeakGradient v G)
    (u : Field) (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u) :
    physicalFieldInner v (laplacian u) =
      -(∑ j : Fin 3, physicalFieldInner (fun x => G x (unitVector j))
        (coordinateDerivative u j)) := by
  have hj (j : Fin 3) :
      physicalFieldInner v (coordinateDerivative (coordinateDerivative u j) j) =
        -physicalFieldInner (fun x => G x (unitVector j)) (coordinateDerivative u j) :=
    hv.integration_by_parts (coordinateDerivative u j) (coordinateDerivative_smooth hu j)
      (coordinateDerivative_spatialPeriodic j u hup) j
  change (∫ x in unitCube, inner ℝ (v x)
    (∑ j : Fin 3, coordinateDerivative (coordinateDerivative u j) j x)) = _
  simp_rw [inner_sum]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    criticalWeakFieldInner_integrable v (coordinateDerivative (coordinateDerivative u j) j)
      hv.velocity_L2 (coordinateDerivative_continuous (coordinateDerivative_smooth hu j) j))]
  change (∑ j : Fin 3, physicalFieldInner v
    (coordinateDerivative (coordinateDerivative u j) j)) = _
  simp_rw [hj]
  simp only [Finset.sum_neg_distrib]

end

end SingularClosure
