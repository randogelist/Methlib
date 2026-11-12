import SingularClosure.PhysicalBilinear
import SingularClosure.SmoothFourierLaplacian

/-!
Actual integrated weak momentum and testing against a positive-time smooth
solution.  Every pairing is an integral on the physical unit cube.  The weak
formulation quantifies over all jointly smooth positive-time periodic
solenoidal velocity tests and separately requires integrability of its three
time integrands.  No relative-energy inequality or uniqueness conclusion is
included in the definition.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Interval Topology

namespace SingularClosure

noncomputable section

/-- Smooth tests on the open positive-time spacetime domain. -/
structure CriticalPositiveSolenoidalTest (φ : Velocity) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => φ z.1 z.2) {z | 0 < z.1}
  periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (φ t)
  solenoidal : ∀ t : ℝ, 0 < t → ∀ x : Vec, divergence (φ t) x = 0

theorem CriticalPositiveSolenoidalTest.spatial_smooth {φ : Velocity}
    (hφ : CriticalPositiveSolenoidalTest φ) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (φ t) := by
  rw [← contDiffOn_univ]
  exact hφ.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ht)

/-- The actual tensor test pairing, with only the smooth test differentiated. -/
def criticalWeakTransport (v φ : Field) : ℝ :=
  ∫ x in unitCube, inner ℝ (v x) ((fderiv ℝ φ x) (v x))

def criticalWeakMomentumIntegrand (ν : ℝ) (v φ : Velocity) (t : ℝ) : ℝ :=
  physicalFieldInner (v t) (timeDerivative φ t) +
    ν * physicalFieldInner (v t) (laplacian (φ t)) +
      criticalWeakTransport (v t) (φ t)

private theorem criticalWeak_continuous_memLp_cube {E : Type*} [NormedAddCommGroup E]
    (f : Vec → E) (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict unitCube) := by
  haveI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_unitCube.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := isCompact_unitCube.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
  exact hC x hx

/-- An L2 velocity may be paired with any continuous physical test. -/
theorem criticalWeakFieldInner_integrable (v φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hφ : Continuous φ) :
    IntegrableOn (fun x => inner ℝ (v x) (φ x)) unitCube volume := by
  have hφ₂ := criticalWeak_continuous_memLp_cube φ hφ 2
  have hi : Integrable (fun x => ‖v x‖ * ‖φ x‖) (volume.restrict unitCube) :=
    hv.norm.integrable_mul (q := 2) hφ₂.norm
  apply hi.mono' (hv.aestronglyMeasurable.inner hφ.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) (v x) (φ x)

/-- The genuine quadratic tensor test is integrable for every L2 velocity. -/
theorem criticalWeakTransport_integrable (v φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hφ : ContDiff ℝ ∞ φ) :
    IntegrableOn (fun x => inner ℝ (v x) ((fderiv ℝ φ x) (v x))) unitCube volume := by
  have hd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := isCompact_unitCube.exists_bound_of_continuousOn hd.continuousOn
  have hi : Integrable (fun x => C * (‖v x‖ * ‖v x‖)) (volume.restrict unitCube) :=
    (hv.norm.integrable_mul (q := 2) hv.norm).const_mul C
  have happ : Continuous (fun q : (Vec →L[ℝ] Vec) × Vec => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hD : AEStronglyMeasurable (fun x => (fderiv ℝ φ x) (v x))
      (volume.restrict unitCube) :=
    happ.comp_aestronglyMeasurable
      (hd.aestronglyMeasurable.prodMk hv.aestronglyMeasurable)
  have hm : AEStronglyMeasurable
      (fun x => inner ℝ (v x) ((fderiv ℝ φ x) (v x))) (volume.restrict unitCube) :=
    hv.aestronglyMeasurable.inner hD
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
  calc
    _ ≤ ‖v x‖ * ‖(fderiv ℝ φ x) (v x)‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖v x‖ * (‖fderiv ℝ φ x‖ * ‖v x‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ φ x).le_opNorm (v x)) (norm_nonneg _)
    _ ≤ ‖v x‖ * (C * ‖v x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem criticalWeak_gradient_continuous (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) :
    Continuous (gradient p) := by
  have hd : Continuous (fderiv ℝ p) := hp.continuous_fderiv (by simp)
  have hc : Continuous (fun x : Vec => fun i : Fin 3 => fderiv ℝ p x (unitVector i)) :=
    continuous_pi (fun i => hd.clm_apply continuous_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp hc

/-- Literal integrated weak momentum on every strictly positive time slab.

The separate integrability clauses prevent interpreting an undefined scalar
integral through the totalized Bochner integral.  Weak incompressibility is the
actual annihilation of gradients of all smooth periodic scalar tests. -/
structure CriticalIntegratedWeakMomentum (ν : ℝ) (v : Velocity) : Prop where
  spatial_periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (v t)
  spatial_L2 : ∀ t : ℝ, 0 < t → MemLp (v t) 2 (volume.restrict unitCube)
  gradient_annihilation : ∀ (t : ℝ), 0 < t → ∀ p : Vec → ℝ,
    ContDiff ℝ ∞ p → SpatialPeriodic p → physicalFieldInner (v t) (gradient p) = 0
  test_integrable : ∀ φ : Velocity, CriticalPositiveSolenoidalTest φ →
    ∀ s t : ℝ, 0 < s → s ≤ t →
      IntervalIntegrable (fun r => physicalFieldInner (v r) (timeDerivative φ r)) volume s t ∧
      IntervalIntegrable (fun r => physicalFieldInner (v r) (laplacian (φ r))) volume s t ∧
      IntervalIntegrable (fun r => criticalWeakTransport (v r) (φ r)) volume s t
  momentum : ∀ φ : Velocity, CriticalPositiveSolenoidalTest φ →
    ∀ s t : ℝ, 0 < s → s ≤ t →
      physicalFieldInner (v t) (φ t) - physicalFieldInner (v s) (φ s) =
        ∫ r in s..t, criticalWeakMomentumIntegrand ν v φ r

private theorem criticalWeakFieldInner_sub_right (v f g : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hf : Continuous f) (hg : Continuous g) :
    physicalFieldInner v (f - g) = physicalFieldInner v f - physicalFieldInner v g := by
  unfold physicalFieldInner
  simp_rw [Pi.sub_apply, inner_sub_right]
  exact integral_sub (criticalWeakFieldInner_integrable v f hv hf)
    (criticalWeakFieldInner_integrable v g hv hg)

private theorem criticalWeakFieldInner_smul_right (v f : Field) (c : ℝ) :
    physicalFieldInner v (c • f) = c * physicalFieldInner v f := by
  unfold physicalFieldInner
  simp only [Pi.smul_apply, inner_smul_right]
  exact integral_const_mul _ _

/-- Cross-energy identity against a genuine positive-time classical solution.
The viscosity pairing remains `integral v · laplacian u`; no weak gradient of
`v`, relative-energy inequality, or uniqueness certificate is assumed. -/
theorem CRITICAL_WEAK_CLASSICAL_CROSS_IDENTITY
    (ν : ℝ) (v u : Velocity) (p : Pressure)
    (hv : CriticalIntegratedWeakMomentum ν v)
    (hu : CriticalPositiveSolenoidalTest u)
    (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
    (hp_periodic : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
    (hequation : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + gradient (p r) x =
        ν • laplacian (u r) x)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r =>
      2 * ν * physicalFieldInner (v r) (laplacian (u r)) -
        physicalFieldInner (v r) (convection (u r)) + criticalWeakTransport (v r) (u r))
      volume s t ∧
    physicalFieldInner (v t) (u t) - physicalFieldInner (v s) (u s) =
      ∫ r in s..t,
        2 * ν * physicalFieldInner (v r) (laplacian (u r)) -
          physicalFieldInner (v r) (convection (u r)) + criticalWeakTransport (v r) (u r) := by
  have hpoint (r : ℝ) (hr : r ∈ Icc s t) :
      criticalWeakMomentumIntegrand ν v u r =
        2 * ν * physicalFieldInner (v r) (laplacian (u r)) -
          physicalFieldInner (v r) (convection (u r)) + criticalWeakTransport (v r) (u r) := by
    have hrpos : 0 < r := hs.trans_le hr.1
    have hus := hu.spatial_smooth hrpos
    have hlap : Continuous (laplacian (u r)) := (laplacian_contDiff (u r) hus).continuous
    have hconv : Continuous (convection (u r)) := convection_continuous hus
    have hgrad : Continuous (gradient (p r)) := criticalWeak_gradient_continuous _ (hp r hrpos)
    have htime : timeDerivative u r = ν • laplacian (u r) - convection (u r) - gradient (p r) := by
      funext x
      change timeDerivative u r x =
        ν • laplacian (u r) x - convection (u r) x - gradient (p r) x
      calc
        _ = (timeDerivative u r x + convection (u r) x + gradient (p r) x) -
            convection (u r) x - gradient (p r) x := by abel
        _ = _ := by rw [hequation r hrpos x]
    have hνlap : Continuous (ν • laplacian (u r)) := continuous_const.smul hlap
    have hpair : physicalFieldInner (v r) (timeDerivative u r) =
        ν * physicalFieldInner (v r) (laplacian (u r)) -
          physicalFieldInner (v r) (convection (u r)) := by
      rw [htime,
        criticalWeakFieldInner_sub_right _ _ _ (hv.spatial_L2 r hrpos) (hνlap.sub hconv) hgrad,
        criticalWeakFieldInner_sub_right _ _ _ (hv.spatial_L2 r hrpos) hνlap hconv,
        criticalWeakFieldInner_smul_right,
        hv.gradient_annihilation r hrpos (p r) (hp r hrpos) (hp_periodic r hrpos), sub_zero]
    unfold criticalWeakMomentumIntegrand
    rw [hpair]
    ring
  obtain ⟨hI₁, hI₂, hI₃⟩ := hv.test_integrable u hu s t hs hst
  have hI : IntervalIntegrable (criticalWeakMomentumIntegrand ν v u) volume s t :=
    (hI₁.add (hI₂.const_mul ν)).add hI₃
  refine ⟨?_, ?_⟩
  · apply hI.congr
    intro r hr
    have hr' : r ∈ Ioc s t := by simpa only [uIoc_of_le hst] using hr
    exact hpoint r ⟨hr'.1.le, hr'.2⟩
  · apply (hv.momentum u hu s t hs hst).trans
    apply intervalIntegral.integral_congr
    intro r hr
    exact hpoint r (by simpa only [uIcc_of_le hst] using hr)

end

end SingularClosure
