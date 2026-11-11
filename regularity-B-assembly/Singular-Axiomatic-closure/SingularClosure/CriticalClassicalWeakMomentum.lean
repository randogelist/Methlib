import SingularClosure.CriticalSmoothEnergy
import SingularClosure.CriticalRoughTransport

/-! The actual integrated weak momentum equation follows from positive-time
classical NSE.  Spatial testing, all time integrability, and the fundamental
theorem of calculus are proved before constructing the weak formulation. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

private theorem criticalClassical_positive_isOpen :
    IsOpen {z : ℝ × Vec | 0 < z.1} :=
  isOpen_lt continuous_const continuous_fst

/-- Spatial differentiation preserves joint smoothness at positive time. -/
theorem critical_positive_coordinateDerivative_smooth
    (u : Velocity)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) {z | 0 < z.1})
    (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      {z | 0 < z.1} := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2))
      {z | 0 < z.1} :=
    hu.fderiv_of_isOpen criticalClassical_positive_isOpen (by simp)
  have hA : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (0, unitVector j))
      {z | 0 < z.1} := hD.clm_apply contDiffOn_const
  apply hA.congr
  intro z hz
  have hj : DifferentiableAt ℝ (fun q : ℝ × Vec => u q.1 q.2) z :=
    (hu.contDiffAt (criticalClassical_positive_isOpen.mem_nhds
      (show z ∈ {q : ℝ × Vec | 0 < q.1} from hz))).differentiableAt (by simp)
  have hpath : HasFDerivAt (fun x : Vec => (z.1, x))
      (ContinuousLinearMap.inr ℝ ℝ Vec) z.2 :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2
  have h : HasFDerivAt (fun x : Vec => u z.1 x)
      ((fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z).comp
        (ContinuousLinearMap.inr ℝ ℝ Vec)) z.2 := by
    simpa only [Function.comp_def] using hj.hasFDerivAt.comp z.2 hpath
  have he := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector j)) h.fderiv
  simpa only [coordinateDerivative, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using he

theorem CriticalPositiveSolenoidalTest.laplacian_continuousOn
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u) :
    ContinuousOn (fun z : ℝ × Vec => laplacian (u z.1) z.2) {z | 0 < z.1} := by
  change ContinuousOn (fun z : ℝ × Vec =>
    ∑ j : Fin 3, coordinateDerivative (coordinateDerivative (u z.1) j) j z.2)
      {z | 0 < z.1}
  apply continuousOn_finset_sum
  intro j _
  exact (critical_positive_coordinateDerivative_smooth
    (fun t => coordinateDerivative (u t) j)
    (critical_positive_coordinateDerivative_smooth u hu.smooth j) j).continuousOn

theorem critical_positive_transport_integrand_continuousOn
    {u φ : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (hφ : CriticalPositiveSolenoidalTest φ) :
    ContinuousOn (fun z : ℝ × Vec =>
      inner ℝ (u z.1 z.2) ((fderiv ℝ (φ z.1) z.2) (u z.1 z.2)))
      {z | 0 < z.1} := by
  have hsum : ContinuousOn (fun z : ℝ × Vec =>
      ∑ j : Fin 3, u z.1 z.2 j • coordinateDerivative (φ z.1) j z.2)
      {z | 0 < z.1} := by
    apply continuousOn_finset_sum
    intro j _
    exact ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      hu.smooth.continuousOn).smul
        (critical_positive_coordinateDerivative_smooth φ hφ.smooth j).continuousOn
  have hD : ContinuousOn (fun z : ℝ × Vec =>
      (fderiv ℝ (φ z.1) z.2) (u z.1 z.2)) {z | 0 < z.1} := by
    apply hsum.congr
    intro z _
    exact critical_matrix_apply_eq_sum _ _
  exact hu.smooth.continuousOn.inner hD

theorem criticalPhysicalH1_smooth (u : Field) (hu : ContDiff ℝ ∞ u)
    (hup : SpatialPeriodic u) : CriticalPhysicalH1 u (fderiv ℝ u) := by
  refine ⟨critical_continuous_memLp_cube u hu.continuous 2,
    critical_continuous_memLp_cube _ (hu.continuous_fderiv (by simp)) 2,
    fun _ : ℕ => u, fun _ => hu, fun _ => hup, ?_, ?_⟩
  · simpa only [sub_self, eLpNorm_zero, eLpNorm_zero'] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · change Tendsto (fun _ : ℕ =>
      eLpNorm (fderiv ℝ u - fderiv ℝ u) 2 (volume.restrict unitCube)) atTop (𝓝 0)
    have hz : (fderiv ℝ u - fderiv ℝ u) =
        (fun _ : Vec => (0 : Vec →L[ℝ] Vec)) := by
      funext x
      exact sub_self _
    have hnorm : eLpNorm (fun _ : Vec => (0 : Vec →L[ℝ] Vec)) 2
        (volume.restrict unitCube) = 0 := eLpNorm_zero'
    simpa only [hz, hnorm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

theorem critical_physicalFieldInner_comm (u v : Field) :
    physicalFieldInner u v = physicalFieldInner v u := by
  unfold physicalFieldInner
  apply integral_congr_ae
  exact Eventually.of_forall fun x => (real_inner_comm (u x) (v x)).symm

theorem critical_smooth_laplacian_pairing_symm
    (u v : Field) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : SpatialPeriodic u) (hvp : SpatialPeriodic v) :
    physicalFieldInner u (laplacian v) = physicalFieldInner v (laplacian u) := by
  unfold physicalFieldInner
  rw [critical_integral_inner_laplacian u v hu hv hup hvp,
    critical_integral_inner_laplacian v u hv hu hvp hup]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall fun x => real_inner_comm _ _

theorem critical_positive_pairing_hasDerivAt
    {u φ : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (hφ : CriticalPositiveSolenoidalTest φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalFieldInner (u r) (φ r))
      (physicalFieldInner (u t) (timeDerivative φ t) +
        physicalFieldInner (timeDerivative u t) (φ t)) t := by
  have h := critical_hasDerivAt_real_cube_integral
    (fun r x => inner ℝ (u r x) (φ r x))
    (fun r x => inner ℝ (u r x) (timeDerivative φ r x) +
      inner ℝ (timeDerivative u r x) (φ r x))
    (hu.smooth.continuousOn.inner hφ.smooth.continuousOn)
    ((hu.smooth.continuousOn.inner hφ.timeDerivative_continuousOn).add
      (hu.timeDerivative_continuousOn.inner hφ.smooth.continuousOn))
    (fun r hr x => (hu.time_hasDerivAt r hr x).inner ℝ (hφ.time_hasDerivAt r hr x)) t ht
  have hut : Continuous (timeDerivative u t) :=
    hu.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hφt : Continuous (timeDerivative φ t) :=
    hφ.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  rw [integral_add
    (physicalFieldInner_integrable (u t) (timeDerivative φ t) (hu.spatial_smooth ht).continuous hφt)
    (physicalFieldInner_integrable (timeDerivative u t) (φ t) hut (hφ.spatial_smooth ht).continuous)] at h
  exact h

/-- Every genuine weak test integrand is continuous on positive compact slabs. -/
theorem critical_classical_test_integrable
    {u φ : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => physicalFieldInner (u r) (timeDerivative φ r)) volume s t ∧
    IntervalIntegrable (fun r => physicalFieldInner (u r) (laplacian (φ r))) volume s t ∧
    IntervalIntegrable (fun r => criticalWeakTransport (u r) (φ r)) volume s t := by
  refine ⟨?_, ?_, ?_⟩
  · exact (critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (u r x) (timeDerivative φ r x))
      (hu.smooth.continuousOn.inner hφ.timeDerivative_continuousOn) s t hs).intervalIntegrable_of_Icc hst
  · exact (critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (u r x) (laplacian (φ r) x))
      (hu.smooth.continuousOn.inner hφ.laplacian_continuousOn) s t hs).intervalIntegrable_of_Icc hst
  · exact (critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (u r x) ((fderiv ℝ (φ r) x) (u r x)))
      (critical_positive_transport_integrand_continuousOn hu hφ) s t hs).intervalIntegrable_of_Icc hst

section Classical

variable (ν : ℝ) (u : Velocity) (p : Pressure)
variable (hu : CriticalPositiveSolenoidalTest u)
variable (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
variable (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
variable (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
  timeDerivative u r x + convection (u r) x + gradient (p r) x =
    ν • laplacian (u r) x)

include hu hp hpp hNSE

theorem critical_classical_test_pairing
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ) (t : ℝ) (ht : 0 < t) :
    physicalFieldInner (timeDerivative u t) (φ t) =
      ν * physicalFieldInner (u t) (laplacian (φ t)) + criticalWeakTransport (u t) (φ t) := by
  have hus := hu.spatial_smooth ht
  have hφs := hφ.spatial_smooth ht
  have hud : Continuous (timeDerivative u t) :=
    hu.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hI₁ := physicalFieldInner_integrable (φ t) (timeDerivative u t) hφs.continuous hud
  have hI₂ := physicalFieldInner_integrable (φ t) (convection (u t)) hφs.continuous
    (convection_continuous hus)
  have hI₃ := physicalFieldInner_integrable (φ t) (gradient (p t)) hφs.continuous
    (criticalWeak_gradient_continuous (p t) (hp t ht))
  have hI₁₂ : IntegrableOn (fun x =>
      inner ℝ (φ t x) (timeDerivative u t x) + inner ℝ (φ t x) (convection (u t) x))
      unitCube volume := hI₁.add hI₂
  have heq : timeDerivative u t + convection (u t) + gradient (p t) = ν • laplacian (u t) :=
    funext (fun x => hNSE t ht x)
  have he := congrArg (physicalFieldInner (φ t)) heq
  simp only [physicalFieldInner, Pi.add_apply, inner_add_right,
    Pi.smul_apply, inner_smul_right] at he
  rw [integral_add hI₁₂ hI₃, integral_add hI₁ hI₂, integral_const_mul,
    critical_smooth_integral_inner_gradient_eq_zero (φ t) (p t) hφs (hp t ht)
      (hφ.periodic t ht) (hpp t ht) (hφ.solenoidal t ht)] at he
  have hdiv : ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner (u t) (gradient f) = 0 := by
    intro f hf hfp
    exact critical_smooth_integral_inner_gradient_eq_zero (u t) f hus hf
      (hu.periodic t ht) hfp (hu.solenoidal t ht)
  have hconv := CRITICAL_ROUGH_TRANSPORT_SKEW (u t) (fderiv ℝ (u t)) (φ t)
    (criticalPhysicalH1_smooth (u t) hus (hu.periodic t ht)) hdiv hφs (hφ.periodic t ht)
  change criticalWeakTransport (u t) (φ t) =
    -physicalFieldInner (φ t) (convection (u t)) at hconv
  change physicalFieldInner (φ t) (timeDerivative u t) +
    physicalFieldInner (φ t) (convection (u t)) + 0 =
      ν * physicalFieldInner (φ t) (laplacian (u t)) at he
  rw [critical_smooth_laplacian_pairing_symm (φ t) (u t) hφs hus
    (hφ.periodic t ht) (hu.periodic t ht)] at he
  rw [critical_physicalFieldInner_comm (timeDerivative u t) (φ t)]
  linarith only [he, hconv]

/-- Positive-time classical NSE satisfies the full integrated weak momentum
predicate, including all separate test-integrability clauses. -/
theorem CRITICAL_CLASSICAL_NSE_INTEGRATED_WEAK_MOMENTUM :
    CriticalIntegratedWeakMomentum ν u := by
  refine ⟨hu.periodic, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact critical_continuous_memLp_cube (u t) (hu.spatial_smooth ht).continuous 2
  · intro t ht f hf hfp
    exact critical_smooth_integral_inner_gradient_eq_zero (u t) f
      (hu.spatial_smooth ht) hf (hu.periodic t ht) hfp (hu.solenoidal t ht)
  · intro φ hφ s t hs hst
    exact critical_classical_test_integrable hu hφ s t hs hst
  · intro φ hφ s t hs hst
    obtain ⟨hTime, hLap, hTransport⟩ := critical_classical_test_integrable hu hφ s t hs hst
    have hI : IntervalIntegrable (criticalWeakMomentumIntegrand ν u φ) volume s t :=
      (hTime.add (hLap.const_mul ν)).add hTransport
    have hC : ContinuousOn (fun r => physicalFieldInner (u r) (φ r)) (Icc s t) :=
      critical_real_cube_integral_continuousOn_Icc
        (fun r x => inner ℝ (u r x) (φ r x))
        (hu.smooth.continuousOn.inner hφ.smooth.continuousOn) s t hs
    have hd : ∀ r ∈ Ioo s t,
        HasDerivAt (fun q => physicalFieldInner (u q) (φ q))
          (criticalWeakMomentumIntegrand ν u φ r) r := by
      intro r hr
      have h := critical_positive_pairing_hasDerivAt hu hφ r (hs.trans hr.1)
      have hvalue : physicalFieldInner (u r) (timeDerivative φ r) +
          physicalFieldInner (timeDerivative u r) (φ r) =
            criticalWeakMomentumIntegrand ν u φ r := by
        rw [critical_classical_test_pairing ν u p hu hp hpp hNSE φ hφ r (hs.trans hr.1)]
        unfold criticalWeakMomentumIntegrand
        ring
      rw [hvalue] at h
      exact h
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hC hd hI).symm

end Classical

/-- Changing the velocity only outside positive time preserves the actual
positive-time integrated weak formulation. -/
theorem CriticalIntegratedWeakMomentum.congr_positive
    {ν : ℝ} {u v : Velocity} (hu : CriticalIntegratedWeakMomentum ν u)
    (heq : ∀ t : ℝ, 0 < t → v t = u t) :
    CriticalIntegratedWeakMomentum ν v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [heq t ht]
    exact hu.spatial_periodic t ht
  · intro t ht
    rw [heq t ht]
    exact hu.spatial_L2 t ht
  · intro t ht f hf hfp
    rw [heq t ht]
    exact hu.gradient_annihilation t ht f hf hfp
  · intro φ hφ s t hs hst
    obtain ⟨hTime, hLap, hTransport⟩ := hu.test_integrable φ hφ s t hs hst
    have hpoint (r : ℝ) (hr : r ∈ uIoc s t) : v r = u r := by
      have hr' : r ∈ Ioc s t := by simpa only [uIoc_of_le hst] using hr
      exact heq r (hs.trans hr'.1)
    refine ⟨hTime.congr (fun r hr => ?_), hLap.congr (fun r hr => ?_),
      hTransport.congr (fun r hr => ?_)⟩ <;> rw [hpoint r hr]
  · intro φ hφ s t hs hst
    rw [heq t (hs.trans_le hst), heq s hs, hu.momentum φ hφ s t hs hst]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc s t := by simpa only [uIcc_of_le hst] using hr
    unfold criticalWeakMomentumIntegrand
    rw [heq r (hs.trans_le hr'.1)]

end

end SingularClosure
