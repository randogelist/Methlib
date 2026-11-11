import SingularClosure.CriticalWeakMomentum
import SingularClosure.CriticalSmoothCancellation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Differentiation under the actual cube integral and the energy equality of an
arbitrary positive-time smooth periodic NSE solution.  No Galerkin support,
energy identity, or relative-energy inequality is an assumption.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory Metric
open scoped ContDiff Interval Topology

namespace SingularClosure

noncomputable section

private theorem critical_positive_of_mem_half_ball {t r : ℝ} (ht : 0 < t)
    (hr : r ∈ closedBall t (t / 2)) : 0 < r := by
  have hh : |r - t| ≤ t / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
  have hl := (abs_le.mp hh).1
  linarith

/-- Local dominated differentiation, with domination derived from a compact
positive-time neighborhood and the fixed compact cube. -/
theorem critical_hasDerivAt_real_cube_integral
    (F D : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) {z | 0 < z.1})
    (hD : ContinuousOn (fun z : ℝ × Vec => D z.1 z.2) {z | 0 < z.1})
    (hd : ∀ t : ℝ, 0 < t → ∀ x : Vec, HasDerivAt (fun r => F r x) (D t x) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x in unitCube, F r x)
      (∫ x in unitCube, D t x) t := by
  have hFc (r : ℝ) (hr : 0 < r) : Continuous (F r) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hDc (r : ℝ) (hr : 0 < r) : Continuous (D r) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hsubset : closedBall t (t / 2) ×ˢ unitCube ⊆ {z : ℝ × Vec | 0 < z.1} := by
    intro z hz
    exact critical_positive_of_mem_half_ball ht hz.1
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (t / 2)).prod isCompact_unitCube).
    exists_bound_of_continuousOn (hD.mono hsubset)
  have hbound : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t (t / 2), ‖D r x‖ ≤ C := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    intro r hr
    exact hC (r, x) ⟨hr, hx⟩
  have hdiff : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t (t / 2), HasDerivAt (fun q => F q x) (D r x) r :=
    Filter.Eventually.of_forall fun x r hr =>
      hd r (critical_positive_of_mem_half_ball ht hr) x
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) (volume.restrict unitCube) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact (hFc r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict unitCube) (F := F) (F' := D)
    (bound := fun _ : Vec => C)
    (closedBall_mem_nhds t (by linarith : 0 < t / 2)) hmeas
    ((hFc t ht).continuousOn.integrableOn_compact isCompact_unitCube)
    (hDc t ht).aestronglyMeasurable hbound
    (continuous_const.continuousOn.integrableOn_compact isCompact_unitCube) hdiff).2

/-- Continuous dependence of a cube integral on a positive compact time slab. -/
theorem critical_real_cube_integral_continuousOn_Icc
    (F : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) {z | 0 < z.1})
    (s t : ℝ) (hs : 0 < s) :
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc s t) := by
  have hsubset : Icc s t ×ˢ unitCube ⊆ {z : ℝ × Vec | 0 < z.1} := by
    intro z hz
    exact hs.trans_le hz.1.1
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_unitCube).
    exists_bound_of_continuousOn (hF.mono hsubset)
  apply continuousOn_of_dominated (μ := volume.restrict unitCube) (bound := fun _ : Vec => C)
  · intro r hr
    have hc : Continuous (F r) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => hs.trans_le hr.1)
    exact hc.aestronglyMeasurable
  · intro r hr
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact hC (r, x) ⟨hr, hx⟩
  · exact continuous_const.continuousOn.integrableOn_compact isCompact_unitCube
  · filter_upwards with x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => hs.trans_le hr.1)

/-- Norm-square differentiation uses the actual pointwise time derivative. -/
theorem critical_physicalEnergy_hasDerivAt_of_joint
    (u d : Velocity)
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) {z | 0 < z.1})
    (hd : ContinuousOn (fun z : ℝ × Vec => d z.1 z.2) {z | 0 < z.1})
    (hderiv : ∀ t : ℝ, 0 < t → ∀ x : Vec, HasDerivAt (fun r => u r x) (d t x) t)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalEnergy (u r))
      (2 * physicalFieldInner (u t) (d t)) t := by
  have h := critical_hasDerivAt_real_cube_integral
    (fun r x => ‖u r x‖ ^ 2) (fun r x => 2 * inner ℝ (u r x) (d r x))
    (hu.norm.pow 2) (continuousOn_const.mul (hu.inner hd))
    (fun r hr x => (hderiv r hr x).norm_sq) t ht
  simpa only [physicalEnergy_eq_integral_norm_sq, physicalFieldInner, integral_const_mul] using h

private theorem critical_positive_spacetime_isOpen :
    IsOpen {z : ℝ × Vec | 0 < z.1} :=
  isOpen_lt continuous_const continuous_fst

/-- The actual partial-time derivative is the joint Fréchet derivative in the
time direction; at positive time the within-Ici derivative is ordinary. -/
theorem CriticalPositiveSolenoidalTest.timeDerivative_eq
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (t : ℝ) (ht : 0 < t) (x : Vec) :
    timeDerivative u t x =
      fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) (1, 0) := by
  have hj : DifferentiableAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
    (hu.smooth.contDiffAt (critical_positive_spacetime_isOpen.mem_nhds ht)).
      differentiableAt (by simp)
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h : HasDerivAt (fun r => u r x)
      (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) (1, 0)) t := by
    simpa only [Function.comp_def] using hj.hasFDerivAt.comp_hasDerivAt t hpath
  change derivWithin (fun r => u r x) (Ici (0 : ℝ)) t = _
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht), h.deriv]

theorem CriticalPositiveSolenoidalTest.time_hasDerivAt
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (t : ℝ) (ht : 0 < t) (x : Vec) :
    HasDerivAt (fun r => u r x) (timeDerivative u t x) t := by
  have hj : DifferentiableAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
    (hu.smooth.contDiffAt (critical_positive_spacetime_isOpen.mem_nhds ht)).
      differentiableAt (by simp)
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  rw [hu.timeDerivative_eq t ht x]
  simpa only [Function.comp_def] using hj.hasFDerivAt.comp_hasDerivAt t hpath

theorem CriticalPositiveSolenoidalTest.timeDerivative_continuousOn
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u) :
    ContinuousOn (fun z : ℝ × Vec => timeDerivative u z.1 z.2) {z | 0 < z.1} := by
  have hfd : ContinuousOn (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2)) {z | 0 < z.1} :=
    hu.smooth.continuousOn_fderiv_of_isOpen critical_positive_spacetime_isOpen (by simp)
  have happ : ContinuousOn
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (1, 0))
      {z | 0 < z.1} := hfd.clm_apply continuousOn_const
  apply happ.congr
  intro z hz
  exact hu.timeDerivative_eq z.1 hz z.2

/-- Smoothness itself supplies the continuity and pointwise derivative inputs
of differentiation under the physical energy integral. -/
theorem CriticalPositiveSolenoidalTest.physicalEnergy_hasDerivAt
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalEnergy (u r))
      (2 * physicalFieldInner (u t) (timeDerivative u t)) t :=
  critical_physicalEnergy_hasDerivAt_of_joint u (timeDerivative u)
    hu.smooth.continuousOn hu.timeDerivative_continuousOn hu.time_hasDerivAt t ht

section Classical

variable (ν : ℝ) (u : Velocity) (p : Pressure)
variable (hu : CriticalPositiveSolenoidalTest u)
variable (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
variable (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
variable (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
  timeDerivative u r x + convection (u r) x + gradient (p r) x =
    ν • laplacian (u r) x)

include hu hp hpp hNSE

/-- The actual smooth NSE has the exact physical energy pairing. -/
theorem critical_smooth_energy_pairing (t : ℝ) (ht : 0 < t) :
    physicalFieldInner (u t) (timeDerivative u t) = -ν * physicalDissipation (u t) := by
  have hus := hu.spatial_smooth ht
  have hud : Continuous (timeDerivative u t) :=
    hu.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hconv : Continuous (convection (u t)) := convection_continuous hus
  have hgrad : Continuous (gradient (p t)) := criticalWeak_gradient_continuous _ (hp t ht)
  have hI₁ := physicalFieldInner_integrable (u t) (timeDerivative u t) hus.continuous hud
  have hI₂ := physicalFieldInner_integrable (u t) (convection (u t)) hus.continuous hconv
  have hI₃ := physicalFieldInner_integrable (u t) (gradient (p t)) hus.continuous hgrad
  have heq : timeDerivative u t + convection (u t) + gradient (p t) = ν • laplacian (u t) :=
    funext (fun x => hNSE t ht x)
  have h := congrArg (physicalFieldInner (u t)) heq
  simp only [physicalFieldInner, Pi.add_apply, inner_add_right,
    Pi.smul_apply, inner_smul_right] at h
  rw [integral_add (hI₁.add hI₂) hI₃, integral_add hI₁ hI₂, integral_const_mul] at h
  rw [critical_smooth_integral_inner_convection_eq_zero
      (u t) hus (hu.periodic t ht) (hu.solenoidal t ht),
    critical_smooth_integral_inner_gradient_eq_zero (u t) (p t) hus (hp t ht)
      (hu.periodic t ht) (hpp t ht) (hu.solenoidal t ht),
    critical_integral_inner_laplacian_self (u t) hus (hu.periodic t ht)] at h
  change (∫ x in unitCube, inner ℝ (u t x) (timeDerivative u t x)) = _
  linarith

/-- Differential energy equality for an arbitrary positive-time smooth NSE. -/
theorem CRITICAL_SMOOTH_NSE_ENERGY_HAS_DERIV (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalEnergy (u r))
      ((-2 * ν) * physicalDissipation (u t)) t := by
  have h := hu.physicalEnergy_hasDerivAt t ht
  rw [critical_smooth_energy_pairing ν u p hu hp hpp hNSE t ht] at h
  convert h using 1 <;> ring

/-- Exact physical energy plus accumulated dissipation on every positive-time
closed slab.  Integrability is derived from the smooth solution. -/
theorem CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY (hν : 0 < ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t ∧
      physicalEnergy (u t) + 2 * ν * (∫ r in s..t, physicalDissipation (u r)) =
        physicalEnergy (u s) := by
  have hP : ContinuousOn (fun r => physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (u r x) (timeDerivative u r x))
      (hu.smooth.continuousOn.inner hu.timeDerivative_continuousOn) s t hs
  have hscaled : ContinuousOn
      (fun r => (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    continuousOn_const.mul hP
  have hD : ContinuousOn (fun r => physicalDissipation (u r)) (Icc s t) := by
    apply hscaled.congr
    intro r hr
    change physicalDissipation (u r) =
      (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)
    rw [critical_smooth_energy_pairing ν u p hu hp hpp hNSE r (hs.trans_le hr.1)]
    simp only [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hν.ne'), one_mul]
  have hE : ContinuousOn (fun r => physicalEnergy (u r)) (Icc s t) := by
    intro r hr
    exact (hu.physicalEnergy_hasDerivAt r (hs.trans_le hr.1)).continuousAt.continuousWithinAt
  have hDI : IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t :=
    hD.intervalIntegrable_of_Icc hst
  refine ⟨hDI, ?_⟩
  have hd : ∀ r ∈ Ioo s t, HasDerivAt (fun q => physicalEnergy (u q))
      ((-2 * ν) * physicalDissipation (u r)) r := by
    intro r hr
    exact CRITICAL_SMOOTH_NSE_ENERGY_HAS_DERIV ν u p hu hp hpp hNSE r (hs.trans hr.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hE hd
    (hDI.const_mul (-2 * ν))
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

end Classical

end

end SingularClosure
