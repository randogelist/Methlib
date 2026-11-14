import QuasiFeffermanB.Endpoints.WeakH0Limit
import QuasiFeffermanB.Endpoints.FiniteTimeTest
import QuasiFeffermanB.Endpoints.TestProjection
import QuasiFeffermanB.EnergyGlobalLimit
import QuasiFeffermanB.EnergyTransportContinuity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Actual physical weak momentum from genuine Galerkin trajectories.
The hypotheses are ordinary energy bounds, cofinal cutoffs, all-time modal
convergence and compatible strong spacetime convergence. No initial-trace,
H1-selection, coordinate-continuity or nonlinear modal-limit premise occurs.

R4 source candidate: no local Lean execution and no matching external audit.
Every declaration below has a body; external elaboration remains required.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology Interval ENNReal ContDiff

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

local notation "μQ" => volume.restrict unitCube

private instance energyPMCubeFinite : IsFiniteMeasure μQ :=
  ⟨by simpa only [Measure.restrict_apply_univ] using
    isCompact_unitCube.measure_lt_top (μ := volume)⟩

private theorem energyPM_velocity_memLp
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (r : ℝ) :
    MemLp (g.velocity r) 2 μQ := by
  change MemLp (finiteSynthesis N (g.coeff r)) 2 μQ
  exact critical_continuous_memLp_cube _ (finiteSynthesis_contDiff N _).continuous 2

private theorem energyPM_velocity_energy_bound
    {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (R : ℝ) (hR : 0 ≤ R)
    (hinit : coefficientEnergy N (g.coeff 0) ≤ R ^ 2)
    (r : ℝ) (hr : 0 ≤ r) :
    physicalEnergy (g.velocity r) ≤ (‖energyH0PhysicalMap‖ * R) ^ 2 := by
  have hv := energyPM_velocity_memLp g r
  rw [physicalEnergy_eq_toLp_norm_sq _ hv,
    ← criticalL2Representative_eq _ hv, energy_galerkin_physical_L2 g r hr]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact (energyH0PhysicalMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      (galerkin_H0_energy_bound hν g R hR hinit r hr) (norm_nonneg _))

private theorem energyPM_pairing_rep (v φ : Field)
    (hv : MemLp v 2 μQ) (hφ : MemLp φ 2 μQ) :
    physicalFieldInner v φ =
      inner ℝ (criticalL2Representative v) (criticalL2Representative φ) := by
  rw [criticalL2Representative_eq _ hv, criticalL2Representative_eq _ hφ]
  exact critical_physicalFieldInner_eq_L2_inner v φ hv hφ

private theorem energyPM_transport_rep (v φ : Field) (hv : MemLp v 2 μQ) :
    criticalWeakTransport (criticalL2Representative v : Field) φ =
      criticalWeakTransport v φ := by
  rw [criticalL2Representative_eq _ hv]
  exact energyWeakTransport_congr_ae hv.coeFn_toLp

private theorem energyPM_pairing_tendsto
    (v : ℕ → Field) (w φ : Field)
    (hv : ∀ n, MemLp (v n) 2 μQ) (hw : MemLp w 2 μQ) (hφ : MemLp φ 2 μQ)
    (hconv : Tendsto (fun n => criticalL2Representative (v n)) atTop
      (𝓝 (criticalL2Representative w))) :
    Tendsto (fun n => physicalFieldInner (v n) φ) atTop
      (𝓝 (physicalFieldInner w φ)) := by
  have heq (n : ℕ) : physicalFieldInner (v n) φ =
      inner ℝ (criticalL2Representative (v n)) (criticalL2Representative φ) :=
    energyPM_pairing_rep (v n) φ (hv n) hφ
  have h : Tendsto
      (fun n => inner ℝ (criticalL2Representative (v n)) (criticalL2Representative φ))
      atTop (𝓝 (inner ℝ (criticalL2Representative w) (criticalL2Representative φ))) :=
    hconv.inner
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => criticalL2Representative φ)
        atTop (𝓝 (criticalL2Representative φ)))
  simpa only [heq, energyPM_pairing_rep w φ hw hφ] using h

private theorem energyPM_transport_tendsto
    (v : ℕ → Field) (w φ : Field)
    (hv : ∀ n, MemLp (v n) 2 μQ) (hw : MemLp w 2 μQ)
    (hφ : ContDiff ℝ ∞ φ)
    (hconv : Tendsto (fun n => criticalL2Representative (v n)) atTop
      (𝓝 (criticalL2Representative w))) :
    Tendsto (fun n => criticalWeakTransport (v n) φ) atTop
      (𝓝 (criticalWeakTransport w φ)) := by
  have h := energyWeakTransport_L2_tendsto
    (fun n => criticalL2Representative (v n)) (criticalL2Representative w) hconv φ hφ
  have heq (n : ℕ) : criticalWeakTransport (criticalL2Representative (v n) : Field) φ =
      criticalWeakTransport (v n) φ := energyPM_transport_rep (v n) φ (hv n)
  simpa only [heq, energyPM_transport_rep w φ hw] using h

private theorem energyPM_test_bound (ψ : Velocity)
    (hψ : ContinuousOn (fun z : ℝ × Vec => ψ z.1 z.2) {z | 0 < z.1})
    (s t : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc s t, ∀ x ∈ unitCube, ‖ψ r x‖ ≤ C := by
  have hc : ContinuousOn (fun z : ℝ × Vec => ψ z.1 z.2)
      ((Icc s t) ×ˢ unitCube) :=
    hψ.mono (fun z hz => hs.trans_le hz.1.1)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_unitCube).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr x hx
  exact (hC (r, x) ⟨hr, hx⟩).trans (le_max_left _ _)

private theorem energyPM_pairing_bound (v φ : Field)
    (hv : MemLp v 2 μQ) (hφ : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x ∈ unitCube, ‖φ x‖ ≤ C) :
    ‖physicalFieldInner v φ‖ ≤
      physicalEnergy v + C ^ 2 * (μQ).real Set.univ := by
  have hφ₂ : MemLp φ 2 μQ := critical_continuous_memLp_cube _ hφ 2
  have hsquare : Integrable (fun x => ‖v x‖ ^ 2) μQ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hinner := critical_L2_inner_integrable v φ hv hφ₂
  unfold physicalFieldInner
  calc
    ‖∫ x in unitCube, inner ℝ (v x) (φ x)‖ ≤
        ∫ x in unitCube, ‖inner ℝ (v x) (φ x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in unitCube, (‖v x‖ ^ 2 + C ^ 2) := by
      apply integral_mono_ae hinner.norm (hsquare.add (integrable_const _))
      filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
      change ‖inner ℝ (v x) (φ x)‖ ≤ ‖v x‖ ^ 2 + C ^ 2
      have h := norm_inner_le_norm (𝕜 := ℝ) (v x) (φ x)
      have hmul := mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg (v x))
      nlinarith [sq_nonneg (‖v x‖ - C)]
    _ = physicalEnergy v + C ^ 2 * (μQ).real Set.univ := by
      rw [integral_add hsquare (integrable_const _), integral_const,
        physicalEnergy_eq_integral_norm_sq]
      simp only [smul_eq_mul]
      ring

private theorem energyPM_transport_bound (v φ : Field)
    (hv : MemLp v 2 μQ) (hφ : ContDiff ℝ ∞ φ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ unitCube, ‖fderiv ℝ φ x‖ ≤ C) :
    ‖criticalWeakTransport v φ‖ ≤ C * physicalEnergy v := by
  have hsquare : Integrable (fun x => ‖v x‖ ^ 2) μQ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hinner := criticalWeakTransport_integrable v φ hv hφ
  unfold criticalWeakTransport
  calc
    ‖∫ x in unitCube, inner ℝ (v x) ((fderiv ℝ φ x) (v x))‖ ≤
        ∫ x in unitCube, ‖inner ℝ (v x) ((fderiv ℝ φ x) (v x))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in unitCube, C * ‖v x‖ ^ 2 := by
      apply integral_mono_ae hinner.norm (hsquare.const_mul C)
      filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
      calc
        _ ≤ ‖v x‖ * ‖(fderiv ℝ φ x) (v x)‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ ‖v x‖ * (‖fderiv ℝ φ x‖ * ‖v x‖) :=
          mul_le_mul_of_nonneg_left ((fderiv ℝ φ x).le_opNorm _) (norm_nonneg _)
        _ ≤ ‖v x‖ * (C * ‖v x‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = C * physicalEnergy v := by rw [integral_const_mul, physicalEnergy_eq_integral_norm_sq]

private theorem energyPM_transport_difference_bound (v φ ψ : Field)
    (hv : MemLp v 2 μQ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ unitCube, ‖fderiv ℝ φ x - fderiv ℝ ψ x‖ ≤ C) :
    ‖criticalWeakTransport v φ - criticalWeakTransport v ψ‖ ≤
      C * physicalEnergy v := by
  have hsquare : Integrable (fun x => ‖v x‖ ^ 2) μQ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hiφ := criticalWeakTransport_integrable v φ hv hφ
  have hiψ := criticalWeakTransport_integrable v ψ hv hψ
  unfold criticalWeakTransport
  rw [← integral_sub hiφ hiψ]
  calc
    ‖∫ x in unitCube,
      (inner ℝ (v x) ((fderiv ℝ φ x) (v x)) -
        inner ℝ (v x) ((fderiv ℝ ψ x) (v x)))‖ ≤
        ∫ x in unitCube,
          ‖inner ℝ (v x) ((fderiv ℝ φ x) (v x)) -
            inner ℝ (v x) ((fderiv ℝ ψ x) (v x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in unitCube, C * ‖v x‖ ^ 2 := by
      apply integral_mono_ae (hiφ.sub hiψ).norm (hsquare.const_mul C)
      filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
      change ‖inner ℝ (v x) ((fderiv ℝ φ x) (v x)) -
        inner ℝ (v x) ((fderiv ℝ ψ x) (v x))‖ ≤ C * ‖v x‖ ^ 2
      rw [← inner_sub_right, ← ContinuousLinearMap.sub_apply]
      calc
        _ ≤ ‖v x‖ * ‖(fderiv ℝ φ x - fderiv ℝ ψ x) (v x)‖ :=
          norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ ‖v x‖ * (‖fderiv ℝ φ x - fderiv ℝ ψ x‖ * ‖v x‖) :=
          mul_le_mul_of_nonneg_left
            ((fderiv ℝ φ x - fderiv ℝ ψ x).le_opNorm _) (norm_nonneg _)
        _ ≤ ‖v x‖ * (C * ‖v x‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = C * physicalEnergy v := by rw [integral_const_mul, physicalEnergy_eq_integral_norm_sq]

private theorem energyPM_dominated_limit
    {μ : Measure ℝ} [IsFiniteMeasure μ] (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n, ∀ᵐ r ∂μ, ‖F n r‖ ≤ C)
    (hlim : ∀ᵐ r ∂μ, Tendsto (fun n => F n r) atTop (𝓝 (f r))) :
    Integrable f μ ∧
      Tendsto (fun n => ∫ r, F n r ∂μ) atTop (𝓝 (∫ r, f r ∂μ)) := by
  have hm : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  have hb : ∀ᵐ r ∂μ, ‖f r‖ ≤ C := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with r hr hb
    exact le_of_tendsto hr.norm (Eventually.of_forall hb)
  refine ⟨(integrable_const C).mono' hm hb, ?_⟩
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    hF (integrable_const C) hbound hlim

private theorem energyPM_cutoff_transport_error
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (v : ℕ → Field) (hv : ∀ n, MemLp (v n) 2 μQ)
    (B : ℝ) (hB : 0 ≤ B) (henergy : ∀ n, physicalEnergy (v n) ≤ B)
    (r : ℝ) (hr : r ∈ Icc s t) :
    Tendsto (fun n =>
      criticalWeakTransport (v n) (finiteSynthesis (N n) (datumFourierCoeff (φ r))) -
        criticalWeakTransport (v n) (φ r)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (B + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηB : η * B < ε := by
    have hden : B + 1 ≠ 0 := ne_of_gt (by linarith : 0 < B + 1)
    have heq : η * (B + 1) = ε := by dsimp [η]; exact div_mul_cancel₀ _ hden
    nlinarith
  have hu := Metric.tendstoUniformlyOn_iff.mp
    (ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM φ hφ s t hs hst) η hη
  filter_upwards [hN.eventually hu] with n hn
  rw [dist_zero_right]
  have hD : ∀ x ∈ unitCube,
      ‖fderiv ℝ (finiteSynthesis (N n) (datumFourierCoeff (φ r))) x -
        fderiv ℝ (φ r) x‖ ≤ η := by
    intro x hx
    have hh := hn (r, x) ⟨hr, hx⟩
    change dist (fderiv ℝ (φ r) x)
      (fderiv ℝ (finiteSynthesis (N n) (datumFourierCoeff (φ r))) x) < η at hh
    rw [dist_eq_norm, norm_sub_rev] at hh
    exact hh.le
  exact ((energyPM_transport_difference_bound (v n) _ _ (hv n)
    (finiteSynthesis_contDiff _ _) (hφ.spatial_smooth (hs.trans_le hr.1))
    η hη.le hD).trans (mul_le_mul_of_nonneg_left (henergy n) hη.le)).trans_lt hηB

private theorem energyPM_physical_subsequence
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (U : ℝ → TorusSobolev 0) (T : ℝ) (z : EnergyTimeH0L2 T)
    (hz : Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 z))
    (hcompat : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), z r = U r) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T),
        Tendsto (fun n => criticalL2Representative ((g (σ n)).velocity r)) atTop
          (𝓝 (criticalL2Representative (energyPeriodicVelocity U r))) := by
  obtain ⟨σ, hσ, hσlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
  have hrep : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
      (g (σ n)).energyTimeH0L2 T r = (g (σ n)).sobolevState 0 r :=
    ae_all_iff.mpr (fun n => ((g (σ n)).sobolevState_memLp 0 T 2).coeFn_toLp)
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hσlim, hcompat, hrep, ae_restrict_mem measurableSet_Icc]
    with r hr hc hrep hrmem
  have hH0 : Tendsto (fun n => (g (σ n)).sobolevState 0 r) atTop (𝓝 (U r)) := by
    simpa only [hrep, hc] using hr
  have hp := energyH0PhysicalMap.continuous.continuousAt.tendsto.comp hH0
  have heq : (fun n => criticalL2Representative ((g (σ n)).velocity r)) =
      (fun n => energyH0PhysicalMap ((g (σ n)).sobolevState 0 r)) := by
    funext n
    exact energy_galerkin_physical_L2 (g (σ n)) r hrmem.1
  rw [heq, energyPeriodicVelocity_L2 U r]
  simpa only [Function.comp_def, energyH0PhysicalMap_apply] using hp

/-- Passage on one positive slab. The subsequence is selected only after the
slab is fixed; the endpoint pairings use the all-time modal limit. -/
private theorem energyPM_slab
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0) (hN : Tendsto N atTop atTop)
    (hc : ∀ r : ℝ, 0 ≤ r → ∀ k i,
      Tendsto (fun n => (g n).coeff r k i) atTop (𝓝 ((U r).val k i)))
    (htime : ∀ T : ℝ, 0 < T → ∃ z : EnergyTimeH0L2 T,
      Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 z) ∧
      ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), z r = U r)
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (IntervalIntegrable
        (fun r => physicalFieldInner (energyPeriodicVelocity U r) (timeDerivative φ r))
        volume s t ∧
      IntervalIntegrable
        (fun r => physicalFieldInner (energyPeriodicVelocity U r) (laplacian (φ r)))
        volume s t ∧
      IntervalIntegrable
        (fun r => criticalWeakTransport (energyPeriodicVelocity U r) (φ r))
        volume s t) ∧
      physicalFieldInner (energyPeriodicVelocity U t) (φ t) -
        physicalFieldInner (energyPeriodicVelocity U s) (φ s) =
        ∫ r in s..t, criticalWeakMomentumIntegrand ν (energyPeriodicVelocity U) φ r := by
  classical
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨z, hz, hcompat⟩ := htime t ht
  obtain ⟨σ, hσ, hconv⟩ := energyPM_physical_subsequence ν a N g U t z hz hcompat
  let μ : Measure ℝ := volume.restrict (Ioc s t)
  haveI : IsFiniteMeasure μ := ⟨by
    have hfinite : volume (Ioc s t) < ⊤ := lt_of_le_of_lt
      (measure_mono (show Ioc s t ⊆ Icc s t from fun r hr => ⟨hr.1.le, hr.2⟩))
      (isCompact_Icc.measure_lt_top (μ := volume))
    simpa only [μ, Measure.restrict_apply_univ] using hfinite⟩
  have hconv' : ∀ᵐ r ∂μ,
      Tendsto (fun n => criticalL2Representative ((g (σ n)).velocity r)) atTop
        (𝓝 (criticalL2Representative (energyPeriodicVelocity U r))) :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioc s t ⊆ Icc (0 : ℝ) t from fun r hr => ⟨hs.le.trans hr.1.le, hr.2⟩)
      hconv
  have hNσ : Tendsto (fun n => N (σ n)) atTop atTop := hN.comp hσ.tendsto_atTop
  let B : ℝ := (‖energyH0PhysicalMap‖ * R) ^ 2
  have hB : 0 ≤ B := sq_nonneg _
  have henergy (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
      physicalEnergy ((g (σ n)).velocity r) ≤ B :=
    energyPM_velocity_energy_bound hν (g (σ n)) R hR (hinit (σ n)) r hr
  have htime_cont (r : ℝ) (hr : 0 < r) : Continuous (timeDerivative φ r) :=
    hφ.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hlap_cont (r : ℝ) (hr : 0 < r) : Continuous (laplacian (φ r)) :=
    hφ.laplacian_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => hr)
  obtain ⟨Ct, hCt, hCt_bound⟩ :=
    energyPM_test_bound (timeDerivative φ) hφ.timeDerivative_continuousOn s t hs
  obtain ⟨Cl, hCl, hCl_bound⟩ :=
    energyPM_test_bound (fun r => laplacian (φ r)) hφ.laplacian_continuousOn s t hs
  obtain ⟨Cp, hCp, hCp_bound⟩ := ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND φ hφ s t hs hst
  let F₁ : ℕ → ℝ → ℝ := fun n r =>
    physicalFieldInner ((g (σ n)).velocity r) (timeDerivative φ r)
  let F₂ : ℕ → ℝ → ℝ := fun n r =>
    physicalFieldInner ((g (σ n)).velocity r) (laplacian (φ r))
  let F₃ : ℕ → ℝ → ℝ := fun n r =>
    criticalWeakTransport ((g (σ n)).velocity r)
      (finiteSynthesis (N (σ n)) (datumFourierCoeff (φ r)))
  let f₁ : ℝ → ℝ := fun r =>
    physicalFieldInner (energyPeriodicVelocity U r) (timeDerivative φ r)
  let f₂ : ℝ → ℝ := fun r =>
    physicalFieldInner (energyPeriodicVelocity U r) (laplacian (φ r))
  let f₃ : ℝ → ℝ := fun r =>
    criticalWeakTransport (energyPeriodicVelocity U r) (φ r)
  have hfinite (n : ℕ) :
      Integrable (F₁ n) μ ∧ Integrable (F₂ n) μ ∧ Integrable (F₃ n) μ := by
    obtain ⟨h₁, h₂, h₃⟩ :=
      ENERGY_GALERKIN_TIME_TEST_INTEGRABLE (g (σ n)) φ hφ s t hs hst
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp h₁,
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp h₂,
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp h₃⟩
  have hbound₁ (n : ℕ) : ∀ᵐ r ∂μ, ‖F₁ n r‖ ≤ B + Ct ^ 2 * (μQ).real Set.univ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrpos := hs.trans hr.1
    exact (energyPM_pairing_bound _ _ (energyPM_velocity_memLp (g (σ n)) r)
      (htime_cont r hrpos) Ct hCt (hCt_bound r ⟨hr.1.le, hr.2⟩)).trans
        (add_le_add (henergy n r hrpos.le) le_rfl)
  have hbound₂ (n : ℕ) : ∀ᵐ r ∂μ, ‖F₂ n r‖ ≤ B + Cl ^ 2 * (μQ).real Set.univ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrpos := hs.trans hr.1
    exact (energyPM_pairing_bound _ _ (energyPM_velocity_memLp (g (σ n)) r)
      (hlap_cont r hrpos) Cl hCl (hCl_bound r ⟨hr.1.le, hr.2⟩)).trans
        (add_le_add (henergy n r hrpos.le) le_rfl)
  have hbound₃ (n : ℕ) : ∀ᵐ r ∂μ, ‖F₃ n r‖ ≤ Cp * B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (energyPM_transport_bound _ _ (energyPM_velocity_memLp (g (σ n)) r)
      (finiteSynthesis_contDiff _ _) Cp hCp
      (hCp_bound (N (σ n)) r ⟨hr.1.le, hr.2⟩)).trans
        (mul_le_mul_of_nonneg_left (henergy n r (hs.trans hr.1).le) hCp)
  have hlim₁ : ∀ᵐ r ∂μ, Tendsto (fun n => F₁ n r) atTop (𝓝 (f₁ r)) := by
    filter_upwards [hconv', ae_restrict_mem measurableSet_Ioc] with r hr hmem
    exact energyPM_pairing_tendsto (fun n => (g (σ n)).velocity r)
      (energyPeriodicVelocity U r) (timeDerivative φ r)
      (fun n => energyPM_velocity_memLp (g (σ n)) r)
      (energyPeriodicVelocity_memLp U r)
      (critical_continuous_memLp_cube _ (htime_cont r (hs.trans hmem.1)) 2) hr
  have hlim₂ : ∀ᵐ r ∂μ, Tendsto (fun n => F₂ n r) atTop (𝓝 (f₂ r)) := by
    filter_upwards [hconv', ae_restrict_mem measurableSet_Ioc] with r hr hmem
    exact energyPM_pairing_tendsto (fun n => (g (σ n)).velocity r)
      (energyPeriodicVelocity U r) (laplacian (φ r))
      (fun n => energyPM_velocity_memLp (g (σ n)) r)
      (energyPeriodicVelocity_memLp U r)
      (critical_continuous_memLp_cube _ (hlap_cont r (hs.trans hmem.1)) 2) hr
  have hlim₃ : ∀ᵐ r ∂μ, Tendsto (fun n => F₃ n r) atTop (𝓝 (f₃ r)) := by
    filter_upwards [hconv', ae_restrict_mem measurableSet_Ioc] with r hr hmem
    have hfixed := energyPM_transport_tendsto (fun n => (g (σ n)).velocity r)
      (energyPeriodicVelocity U r) (φ r)
      (fun n => energyPM_velocity_memLp (g (σ n)) r)
      (energyPeriodicVelocity_memLp U r) (hφ.spatial_smooth (hs.trans hmem.1)) hr
    have herror := energyPM_cutoff_transport_error φ hφ s t hs hst
      (fun n => N (σ n)) hNσ (fun n => (g (σ n)).velocity r)
      (fun n => energyPM_velocity_memLp (g (σ n)) r) B hB
      (fun n => henergy n r (hs.trans hmem.1).le) r ⟨hmem.1.le, hmem.2⟩
    simpa only [sub_add_cancel, zero_add] using herror.add hfixed
  obtain ⟨hi₁, hj₁⟩ := energyPM_dominated_limit F₁ f₁
    (B + Ct ^ 2 * (μQ).real Set.univ) (fun n => (hfinite n).1.aestronglyMeasurable)
    hbound₁ hlim₁
  obtain ⟨hi₂, hj₂⟩ := energyPM_dominated_limit F₂ f₂
    (B + Cl ^ 2 * (μQ).real Set.univ) (fun n => (hfinite n).2.1.aestronglyMeasurable)
    hbound₂ hlim₂
  obtain ⟨hi₃, hj₃⟩ := energyPM_dominated_limit F₃ f₃
    (Cp * B) (fun n => (hfinite n).2.2.aestronglyMeasurable) hbound₃ hlim₃
  have hI₁ : IntervalIntegrable f₁ volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hi₁
  have hI₂ : IntervalIntegrable f₂ volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hi₂
  have hI₃ : IntervalIntegrable f₃ volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hi₃
  have hJ₁ : Tendsto (fun n => ∫ r in s..t, F₁ n r) atTop (𝓝 (∫ r in s..t, f₁ r)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hj₁
  have hJ₂ : Tendsto (fun n => ∫ r in s..t, F₂ n r) atTop (𝓝 (∫ r in s..t, f₂ r)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hj₂
  have hJ₃ : Tendsto (fun n => ∫ r in s..t, F₃ n r) atTop (𝓝 (∫ r in s..t, f₃ r)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hj₃
  have hright := (hJ₁.add (hJ₂.const_mul ν)).add hJ₃
  have hleft :=
    ((ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO ν hν a N g R hR hinit U hc t ht.le
      (φ t) (critical_continuous_memLp_cube _ (hφ.spatial_smooth ht).continuous 2)).sub
     (ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO ν hν a N g R hR hinit U hc s hs.le
      (φ s) (critical_continuous_memLp_cube _ (hφ.spatial_smooth hs).continuous 2))).comp
        hσ.tendsto_atTop
  have hid (n : ℕ) :
      physicalFieldInner ((g (σ n)).velocity t) (φ t) -
        physicalFieldInner ((g (σ n)).velocity s) (φ s) =
      (∫ r in s..t, F₁ n r) + ν * (∫ r in s..t, F₂ n r) +
        (∫ r in s..t, F₃ n r) := by
    have h := ENERGY_GALERKIN_TIME_TEST_IDENTITY (g (σ n)) φ hφ s t hs hst
    obtain ⟨h₁, h₂, h₃⟩ :=
      ENERGY_GALERKIN_TIME_TEST_INTEGRABLE (g (σ n)) φ hφ s t hs hst
    rw [intervalIntegral.integral_add (h₁.add (h₂.const_mul ν)) h₃,
      intervalIntegral.integral_add h₁ (h₂.const_mul ν),
      intervalIntegral.integral_const_mul] at h
    exact h
  have heq : (fun n =>
      physicalFieldInner ((g (σ n)).velocity t) (φ t) -
        physicalFieldInner ((g (σ n)).velocity s) (φ s)) =
      (fun n => (∫ r in s..t, F₁ n r) + ν * (∫ r in s..t, F₂ n r) +
        (∫ r in s..t, F₃ n r)) := funext hid
  have hleft' : Tendsto
      (fun n => (∫ r in s..t, F₁ n r) + ν * (∫ r in s..t, F₂ n r) +
        (∫ r in s..t, F₃ n r)) atTop
      (𝓝 (physicalFieldInner (energyPeriodicVelocity U t) (φ t) -
        physicalFieldInner (energyPeriodicVelocity U s) (φ s))) := by
    change Tendsto
      (fun n => physicalFieldInner ((g (σ n)).velocity t) (φ t) -
        physicalFieldInner ((g (σ n)).velocity s) (φ s)) atTop
      (𝓝 (physicalFieldInner (energyPeriodicVelocity U t) (φ t) -
        physicalFieldInner (energyPeriodicVelocity U s) (φ s))) at hleft
    rw [heq] at hleft
    exact hleft
  refine ⟨⟨hI₁, hI₂, hI₃⟩, ?_⟩
  have he := tendsto_nhds_unique hleft' hright
  change _ = ∫ r in s..t, (f₁ r + ν * f₂ r + f₃ r)
  rw [intervalIntegral.integral_add (hI₁.add (hI₂.const_mul ν)) hI₃,
    intervalIntegral.integral_add hI₁ (hI₂.const_mul ν),
    intervalIntegral.integral_const_mul]
  exact he

/-- The actual physical weak momentum endpoint. The only compactness input
is compatible strong spacetime convergence of genuine Galerkin solutions.
All endpoint pairings retain the prescribed all-time modal representative. -/
theorem ENERGY_GALERKIN_PHYSICAL_MOMENTUM
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0) (hN : Tendsto N atTop atTop)
    (hc : ∀ r : ℝ, 0 ≤ r → ∀ k i,
      Tendsto (fun n => (g n).coeff r k i) atTop (𝓝 ((U r).val k i)))
    (htime : ∀ T : ℝ, 0 < T → ∃ z : EnergyTimeH0L2 T,
      Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 z) ∧
      ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), z r = U r) :
    CriticalIntegratedWeakMomentum ν (energyPeriodicVelocity U) := by
  have hspec (r : ℝ) (hr : 0 ≤ r) := energy_modal_limit_constraints ν a N g U hc r hr
  refine
    { spatial_periodic := fun r _ => energyPeriodicField_periodic (U r)
      spatial_L2 := fun r _ => energyPeriodicVelocity_memLp U r
      gradient_annihilation := ?_
      test_integrable := ?_
      momentum := ?_ }
  · intro r hr p hp hpp
    exact energyPeriodicField_gradient_annihilation (U r)
      (hspec r hr.le).1 (hspec r hr.le).2.1 (hspec r hr.le).2.2 p hp hpp
  · intro φ hφ s t hs hst
    exact (energyPM_slab ν hν a N g R hR hinit U hN hc htime φ hφ s t hs hst).1
  · intro φ hφ s t hs hst
    exact (energyPM_slab ν hν a N g R hR hinit U hN hc htime φ hφ s t hs hst).2

end
end QuasiFeffermanB

