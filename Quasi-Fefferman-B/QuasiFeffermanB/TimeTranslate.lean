import SingularClosure.CriticalSmoothEnergy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Literal translation of the native integrated weak momentum equation.
The translated test is extended by a smooth positive time reparametrization.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval ContDiff

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def timeTranslate {E : Type*} (s : ℝ) (f : ℝ → E) : ℝ → E :=
  fun t => f (t + s)

def restartTimeClamp (s c r : ℝ) : ℝ :=
  c + Real.smoothTransition ((r - s - c) / c) * (r - s - c)

theorem restartTimeClamp_pos (s : ℝ) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    0 < restartTimeClamp s c r := by
  unfold restartTimeClamp
  by_cases hy : r - s - c ≤ 0
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hy hc.le)]
    simpa using hc
  · have hprod := mul_nonneg (Real.smoothTransition.nonneg ((r - s - c) / c))
      (le_of_not_ge hy)
    linarith

theorem restartTimeClamp_contDiff (s c : ℝ) : ContDiff ℝ ∞ (restartTimeClamp s c) := by
  unfold restartTimeClamp
  exact contDiff_const.add
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).sub contDiff_const).div_const c)).mul
        ((contDiff_id.sub contDiff_const).sub contDiff_const))

theorem restartTimeClamp_eq (s : ℝ) {c r : ℝ} (hc : 0 < c)
    (hr : 2 * c ≤ r - s) : restartTimeClamp s c r = r - s := by
  have hratio : 1 ≤ (r - s - c) / c := (le_div_iff₀ hc).mpr (by linarith)
  unfold restartTimeClamp
  rw [Real.smoothTransition.one_of_one_le hratio]
  ring

theorem restartTimeClamp_hasDerivAt (s : ℝ) {c r : ℝ} (hc : 0 < c)
    (hr : 2 * c < r - s) : HasDerivAt (restartTimeClamp s c) 1 r := by
  have heq : restartTimeClamp s c =ᶠ[𝓝 r] (fun q : ℝ => q - s) := by
    filter_upwards [Ioi_mem_nhds (show s + 2 * c < r by linarith)] with q hq
    exact restartTimeClamp_eq s hc (by linarith)
  exact ((hasDerivAt_id r).sub_const s).congr_of_eventuallyEq heq

def restartTest (s c : ℝ) (φ : Velocity) : Velocity :=
  fun r => φ (restartTimeClamp s c r)

theorem restartTest_is_test (s : ℝ) {c : ℝ} (hc : 0 < c)
    {φ : Velocity} (hφ : CriticalPositiveSolenoidalTest φ) :
    CriticalPositiveSolenoidalTest (restartTest s c φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hφ.smooth.comp
      (((restartTimeClamp_contDiff s c).comp contDiff_fst).prodMk
        contDiff_snd).contDiffOn
      (fun z _ => restartTimeClamp_pos s hc z.1)
  · intro r hr
    exact hφ.periodic _ (restartTimeClamp_pos s hc r)
  · intro r hr
    exact hφ.solenoidal _ (restartTimeClamp_pos s hc r)

theorem restartTest_eq (s : ℝ) {c r : ℝ} (hc : 0 < c)
    (hr : 2 * c ≤ r - s) (φ : Velocity) :
    restartTest s c φ r = φ (r - s) := by
  unfold restartTest
  rw [restartTimeClamp_eq s hc hr]

theorem restartTest_timeDerivative (s : ℝ) {c r : ℝ} (hc : 0 < c)
    (hr : 2 * c < r - s) (hrpos : 0 < r)
    {φ : Velocity} (hφ : CriticalPositiveSolenoidalTest φ) :
    timeDerivative (restartTest s c φ) r = timeDerivative φ (r - s) := by
  funext x
  have hclamp := restartTimeClamp_hasDerivAt s hc hr
  have hcomp := (hφ.time_hasDerivAt (restartTimeClamp s c r)
    (restartTimeClamp_pos s hc r) x).comp r hclamp
  have hcomp' : HasDerivAt (fun q => restartTest s c φ q x)
      (timeDerivative φ (r - s) x) r := by
    simpa only [Function.comp_def, restartTest, one_smul,
      restartTimeClamp_eq s hc hr.le] using hcomp
  exact ((restartTest_is_test s hc hφ).time_hasDerivAt r hrpos x).unique hcomp'

theorem timeTranslate_integrated_momentum
    {ν : ℝ} {v : Velocity} (hv : CriticalIntegratedWeakMomentum ν v)
    {s : ℝ} (hs : 0 ≤ s) :
    CriticalIntegratedWeakMomentum ν (timeTranslate s v) := by
  refine {
    spatial_periodic := fun t ht => hv.spatial_periodic (t + s) (by linarith)
    spatial_L2 := fun t ht => hv.spatial_L2 (t + s) (by linarith)
    gradient_annihilation := fun t ht p hp hpp =>
      hv.gradient_annihilation (t + s) (by linarith) p hp hpp
    test_integrable := ?_
    momentum := ?_
  }
  · intro φ hφ a b ha hab
    let c : ℝ := a / 4
    have hc : 0 < c := by dsimp [c]; positivity
    let ψ : Velocity := restartTest s c φ
    have hψ : CriticalPositiveSolenoidalTest ψ := restartTest_is_test s hc hφ
    have heq (r : ℝ) (hr : a ≤ r) : ψ (r + s) = φ r := by
      simpa only [add_sub_cancel_right] using
        restartTest_eq s hc (r := r + s) (by dsimp [c]; linarith) φ
    have hd (r : ℝ) (hr : a ≤ r) :
        timeDerivative ψ (r + s) = timeDerivative φ r := by
      simpa only [add_sub_cancel_right] using
        restartTest_timeDerivative s hc (r := r + s)
          (by dsimp [c]; linarith) (by linarith) hφ
    obtain ⟨hI₁, hI₂, hI₃⟩ := hv.test_integrable ψ hψ
      (a + s) (b + s) (by linarith) (by linarith)
    have hI₁' := hI₁.comp_add_right s
    have hI₂' := hI₂.comp_add_right s
    have hI₃' := hI₃.comp_add_right s
    simp only [add_sub_cancel_right] at hI₁' hI₂' hI₃'
    refine ⟨hI₁'.congr ?_, hI₂'.congr ?_, hI₃'.congr ?_⟩
    · intro r hr
      have hr' : r ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hr
      change physicalFieldInner (v (r + s)) (timeDerivative ψ (r + s)) = _
      rw [hd r hr'.1.le]
      rfl
    · intro r hr
      have hr' : r ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hr
      change physicalFieldInner (v (r + s)) (laplacian (ψ (r + s))) = _
      rw [heq r hr'.1.le]
      rfl
    · intro r hr
      have hr' : r ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hr
      change criticalWeakTransport (v (r + s)) (ψ (r + s)) = _
      rw [heq r hr'.1.le]
      rfl
  · intro φ hφ a b ha hab
    let c : ℝ := a / 4
    have hc : 0 < c := by dsimp [c]; positivity
    let ψ : Velocity := restartTest s c φ
    have hψ : CriticalPositiveSolenoidalTest ψ := restartTest_is_test s hc hφ
    have heq (r : ℝ) (hr : a ≤ r) : ψ (r + s) = φ r := by
      simpa only [add_sub_cancel_right] using
        restartTest_eq s hc (r := r + s) (by dsimp [c]; linarith) φ
    have hd (r : ℝ) (hr : a ≤ r) :
        timeDerivative ψ (r + s) = timeDerivative φ r := by
      simpa only [add_sub_cancel_right] using
        restartTest_timeDerivative s hc (r := r + s)
          (by dsimp [c]; linarith) (by linarith) hφ
    change physicalFieldInner (v (b + s)) (φ b) -
      physicalFieldInner (v (a + s)) (φ a) = _
    rw [← heq b hab, ← heq a le_rfl]
    rw [hv.momentum ψ hψ (a + s) (b + s) (by linarith) (by linarith)]
    rw [← intervalIntegral.integral_comp_add_right (criticalWeakMomentumIntegrand ν v ψ) s]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    unfold criticalWeakMomentumIntegrand
    rw [hd r hr'.1, heq r hr'.1]
    rfl

theorem timeTranslate_measurePreserving_Ioc (s T : ℝ) :
    MeasurePreserving (fun t : ℝ => t + s)
      (volume.restrict (Ioc (0 : ℝ) T))
      (volume.restrict (Ioc s (T + s))) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + s) volume volume :=
    ⟨(continuous_id.add continuous_const).measurable, map_add_right_eq_self volume s⟩
  have hpre : (fun t : ℝ => t + s) ⁻¹' Ioc s (T + s) = Ioc (0 : ℝ) T := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [hpre] using hmp.restrict_preimage (s := Ioc s (T + s)) measurableSet_Ioc

theorem timeTranslate_memLp_Ioc
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞}
    {s T : ℝ} (hs : 0 ≤ s)
    (hf : MemLp f p (volume.restrict (Ioc (0 : ℝ) (T + s)))) :
    MemLp (timeTranslate s f) p (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hsub : Ioc s (T + s) ⊆ Ioc (0 : ℝ) (T + s) := by
    intro t ht
    exact ⟨hs.trans_lt ht.1, ht.2⟩
  exact (hf.mono_measure (Measure.restrict_mono_set volume hsub)).comp_measurePreserving
    (timeTranslate_measurePreserving_Ioc s T)

theorem timeTranslate_ae_Ioc {P : ℝ → Prop} {s T : ℝ} (hs : 0 ≤ s)
    (hP : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) (T + s)), P r) :
    ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) T), P (r + s) := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioc).mp hP
  have hrestricted : ∀ᵐ r ∂volume.restrict (Ioc s (T + s)), P r := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hglobal] with r hr
    intro hrs
    exact hr ⟨hs.trans_lt hrs.1, hrs.2⟩
  have hmp := timeTranslate_measurePreserving_Ioc s T
  have hmapped : ∀ᵐ r ∂Measure.map (fun t : ℝ => t + s)
      (volume.restrict (Ioc (0 : ℝ) T)), P r := by
    rw [hmp.map_eq]
    exact hrestricted
  exact ae_of_ae_map hmp.aemeasurable hmapped

end
end QuasiFeffermanB
