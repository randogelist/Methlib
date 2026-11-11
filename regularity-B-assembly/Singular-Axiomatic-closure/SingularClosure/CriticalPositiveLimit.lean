import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalPositiveLimitCalculus
import SingularClosure.CriticalPositiveTimeHighOrder

/-! Construction of the actual positive-time Sobolev flow from a uniform
H0 Galerkin limit. Higher membership is proved by weighted-l2 lower
semicontinuity; one higher bound gives strong continuity. The proved modal
integral equation then identifies the genuine Sobolev-valued derivative. -/

set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SingularClosure
noncomputable section

theorem CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T))
    (hbound : ∀ (s : ℕ) (τ T : ℝ), 0 < τ → τ < T →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (t : ℝ), t ∈ Icc τ T →
        ‖(g n).sobolevState s t‖ ≤ B) :
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t := by
  have hcoeff (s : ℕ) (t : ℝ) (ht : 0 < t) (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => ((g n).sobolevState s t).val k i) atTop (𝓝 ((u t).val k i)) := by
    have h := ((torusSobolevH0Coeff_continuous k i).tendsto (u t)).comp
      ((hconv (t + 1) (by linarith)).tendsto_at ⟨ht.le, by linarith⟩)
    have heq : (fun n => ((g n).sobolevState s t).val k i) =
        (fun n => ((g n).sobolevState 0 t).val k i) := by
      funext n
      rw [(g n).sobolevState_coeff s ht.le, (g n).sobolevState_coeff 0 ht.le]
    rw [heq]
    exact h
  have hmem (s : ℕ) (t : ℝ) (ht : 0 < t) :
      Memℓp (sobolevWeightedCoeff s (u t).val) 2 := by
    obtain ⟨B, _, hb⟩ := hbound s (t / 2) (t + 1) (by positivity) (by linarith)
    exact (torusSobolev_limit_mem_and_norm_le s
      (fun n => (g n).sobolevState s t) (u t).val B
      (fun n => hb n t ⟨by linarith, by linarith⟩) (hcoeff s t ht)).choose
  let U : ∀ s : ℕ, ℝ → TorusSobolev s := fun s t =>
    if ht : 0 < t then ⟨(u t).val, hmem s t ht⟩ else 0
  have hUc (s : ℕ) (t : ℝ) (ht : 0 < t) : (U s t).val = (u t).val := by
    have heq : U s t = (⟨(u t).val, hmem s t ht⟩ : TorusSobolev s) := dif_pos ht
    exact congrArg (fun z : TorusSobolev s => z.val) heq
  have hU0 (t : ℝ) (ht : 0 < t) : U 0 t = u t := Subtype.ext (hUc 0 t ht)
  have hUb (s : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc τ T, ‖U s t‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hbound s τ T hτ hτT
    refine ⟨B, hB, ?_⟩
    intro t ht
    obtain ⟨hc, hn⟩ := torusSobolev_limit_mem_and_norm_le s
      (fun n => (g n).sobolevState s t) (u t).val B
      (fun n => hb n t ht) (hcoeff s t (hτ.trans_le ht.1))
    have heq : U s t = (⟨(u t).val, hc⟩ : TorusSobolev s) :=
      Subtype.ext (hUc s t (hτ.trans_le ht.1))
    rw [heq]
    exact hn
  have hinc (s : ℕ) (t : ℝ) (ht : 0 < t) :
      torusSobolevInclusion s (U (s + 1) t) = U s t := by
    apply Subtype.ext
    rw [torusSobolevInclusion_coeff, hUc (s + 1) t ht, hUc s t ht]
  have hUcc (s : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
      ContinuousOn (U s) (Icc τ T) := by
    obtain ⟨B, _, hb⟩ := hUb (s + 1) τ T hτ hτT
    have hc (k : Frequency) (i : Fin 3) :
        ContinuousOn (fun t => (U (s + 1) t).val k i) (Icc τ T) := by
      apply ((torusSobolevH0Coeff_continuous k i).comp_continuousOn
        (hu.mono (fun t ht => hτ.le.trans ht.1))).congr
      intro t ht
      exact congrArg (fun c : FourierCoeff => c k i) (hUc (s + 1) t (hτ.trans_le ht.1))
    apply (torusSobolevInclusion_continuousOn_of_coeff_continuousOn
      s (U (s + 1)) (Icc τ T) B hb hc).congr
    intro t ht
    exact (hinc s t (hτ.trans_le ht.1)).symm
  have hU : ∀ s : ℕ, ContinuousOn (U s) (Ioi 0) := by
    intro s t ht
    change 0 < t at ht
    have h := hUcc s (t / 2) (t + 1) (by positivity) (by linarith)
      t ⟨by linarith, by linarith⟩
    exact (h.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt
  have hR (s : ℕ) : ContinuousOn
      (fun t => fourierSobolevRhs ν s (U (s + 2) t)) (Ioi 0) :=
    (fourierSobolevRhs_contDiff ν s).continuous.comp_continuousOn (hU (s + 2))
  have hRc (s : ℕ) (t : ℝ) (ht : 0 < t) :
      (fourierSobolevRhs ν s (U (s + 2) t)).val = fullFourierRhs ν (u t) := by
    have hlower : torusSobolevLower 0 (s + 2) (Nat.zero_le _) (U (s + 2) t) = u t := by
      apply Subtype.ext
      rw [torusSobolevLower_coeff]
      exact hUc (s + 2) t ht
    rw [fourierSobolevRhs_coefficient_eq_fullRhs, hlower]
  have heq := criticalGalerkinGlobalLimit_coefficient_integral ν a φ hφ g u hu hconv
  have hd (s : ℕ) (t : ℝ) (ht : 0 < t) :
      HasDerivWithinAt (U s) (fourierSobolevRhs ν s (U (s + 2) t)) (Ioi 0) t :=
    (critical_positive_sobolev_derivative_of_modal_integral ν u hu heq s (U s)
      (fun z => fourierSobolevRhs ν s (U (s + 2) z)) (hUc s) (hR s) (hRc s) t ht).hasDerivWithinAt
  have hlim (t : ℝ) (ht : 0 < t) :
      Tendsto (fun n => (g n).sobolevState 0 t) atTop (𝓝 (u t)) :=
    (hconv (t + 1) (by linarith)).tendsto_at ⟨ht.le, by linarith⟩
  have hreal (t : ℝ) (ht : 0 < t) : SpectralReality (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_reality_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_reality 0 t ht.le))
  have hsol (t : ℝ) (ht : 0 < t) : SpectralSolenoidal (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_solenoidal_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_solenoidal 0 t ht.le))
  have hzero (t : ℝ) (ht : 0 < t) : SpectralMeanZero (U 0 t).val := by
    rw [hUc 0 t ht]
    exact torusSobolevH0_zero_mode_of_tendsto (hlim t ht)
      (Filter.Eventually.of_forall (fun n => (g n).sobolevState_zero_mode 0 t ht.le))
  refine ⟨{
    state := U
    continuous := hU
    coeff := fun s t ht => (hUc s t ht).trans (hUc 0 t ht).symm
    derivative := hd
    reality := hreal
    solenoidal := hsol
    mean_zero := hzero
  }, hU0⟩

theorem SMALL_DATA_POSITIVE_FLOW_OF_H0_LIMIT
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)) :
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t := by
  apply CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g u hu hconv
  intro s τ T hτ hτT
  obtain ⟨B, hB, hb⟩ := SMALL_DATA_POSITIVE_TIME_ALL_ORDERS ν hν a hreal hsmall s τ T hτ hτT
  refine ⟨B + 1, by linarith, ?_⟩
  intro n t ht
  have h := hb (φ n + 1) (g n) t ht
  have hi : 0 ≤ ∫ z in τ..t, highOrderEnergy (s + 1) (φ n + 1) ((g n).coeff z) :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun z => highOrderEnergy_nonneg _ _ _)
  have hn : ‖(g n).sobolevState s t‖ ^ 2 ≤ B := by
    have heq : highOrderEnergy s (φ n + 1) ((g n).coeff t) =
        ‖(g n).sobolevState s t‖ ^ 2 := highOrderEnergy_eq_sobolev_norm_sq _ _ _
    rw [← heq]
    nlinarith [mul_nonneg hν.le hi]
  nlinarith [sq_nonneg (‖(g n).sobolevState s t‖ - 1)]

end
end SingularClosure
