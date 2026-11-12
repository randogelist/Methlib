import QuasiFeffermanB.EnergyGlobalCoefficient
import QuasiFeffermanB.EnergyLimitCompatibility
import SingularClosure.CriticalLimitFatou
import SingularClosure.CriticalUniformBounds

/-! One global energy-level coefficient trajectory and its actual strong
spacetime-L2 and weak-derivative Sobolev representatives. The construction
uses the ordinary Galerkin energy law, never AX6 or critical smallness. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem ENERGY_GALERKIN_GLOBAL_LIMIT
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ U : ℝ → TorusSobolev 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖U t‖ ≤ R) ∧
      (∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0)) ∧
      (∀ T k i, TendstoUniformlyOn (fun n t => (g (φ n)).coeff t k i)
        (fun t => (U t).val k i) atTop (Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 ≤ T → ∃ v : EnergyTimeH0L2 T,
        Tendsto (fun n => (g (φ n)).energyTimeH0L2 T) atTop (𝓝 v) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), v t = U t)) := by
  classical
  obtain ⟨c, φ, hφ, hc, hoverlap⟩ :=
    ENERGY_GALERKIN_GLOBAL_COEFFICIENT_SUBSEQUENCE ν hν.le a N g R hR hinit
  let C := globalEnergyCoefficient c
  have hC (k : Frequency) (i : Fin 3) : ContinuousOn (fun t => C t k i) (Ici 0) :=
    globalEnergyCoefficient_continuousOn c hoverlap k i
  have hconv (T : ℝ) (k : Frequency) (i : Fin 3) :
      TendstoUniformlyOn (fun n t => (g (φ n)).coeff t k i)
        (fun t => C t k i) atTop (Icc (0 : ℝ) T) :=
    globalEnergyCoefficient_uniform_limit ν a N g c φ hc hoverlap T k i
  have hex (t : ℝ) : ∃ v : CriticalSobolev 0, criticalCoeff 0 v = C t ∧ ‖v‖ ≤ R := by
    by_cases ht : 0 ≤ t
    · apply criticalSobolev_limit_mem_and_norm_le (l := (atTop : Filter ℕ)) 0
        (fun n => (g (φ n)).criticalState 0 t) (C t) R
      · intro n
        apply (sq_le_sq₀ (norm_nonneg _) hR).mp
        rw [galerkin_critical_zero_norm_sq]
        exact ((g (φ n)).coefficientEnergy_le_initial hν.le ht).trans (hinit (φ n))
      · intro k i
        have heq (n : ℕ) : criticalCoeff 0 ((g (φ n)).criticalState 0 t) = (g (φ n)).coeff t :=
          (g (φ n)).criticalState_coeff 0 ht
        simpa only [heq] using (hconv (t + 1) k i).tendsto_at ⟨ht, by linarith⟩
    · refine ⟨0, ?_, ?_⟩
      · simp [C, globalEnergyCoefficient, ht]
      · simpa using hR
  choose V hV hVR using hex
  let U : ℝ → TorusSobolev 0 := fun t => criticalH0Equiv (V t)
  have hU (t : ℝ) : (U t).val = C t := by
    rw [U, criticalH0Equiv_coeff, hV t]
  refine ⟨U, φ, hφ, ?_, ?_, ?_, ?_⟩
  · intro t _
    simpa only [U, criticalH0Equiv.norm_map] using hVR t
  · intro k i
    simpa only [hU] using hC k i
  · intro T k i
    simpa only [hU] using hconv T k i
  · intro T hT
    let B : ℝ := T * R ^ 2 + R ^ 2 / (2 * ν)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hcoeff (k : Frequency) (i : Fin 3) : TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i)
        (fun t => (U t.val).val k i) atTop := by
      have heq :
          (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i) =
          (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i) := by
        funext n t
        rw [(g (φ n)).sobolevState_coeff 0 t.property.1]
      rw [heq]
      simpa only [hU] using tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp (hconv T k i)
    have hbudget (n : ℕ) :
        (∫ t in (0 : ℝ)..T, ‖(g (φ n)).sobolevState 1 t‖ ^ 2) ≤ B :=
      galerkin_H1_time_energy_bound hν (g (φ n)) R T hT (hinit (φ n))
    obtain ⟨v, hv⟩ := ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM
      ν (fun n => a (φ n)) (fun n => N (φ n)) (fun n => g (φ n))
      T B hT hB (fun t => U t.val) hcoeff hbudget
    have hcompat := energyGalerkinTimeLimits_compatible
      ν (fun n => a (φ n)) (fun n => N (φ n)) (fun n => g (φ n))
      T (fun t => U t.val) v hcoeff hv
    refine ⟨v, hv, ?_⟩
    filter_upwards [hcompat, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact ht hmem

theorem energy_modal_limit_constraints
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (U : ℝ → TorusSobolev 0)
    (hc : ∀ t, 0 ≤ t → ∀ k i,
      Tendsto (fun n => (g n).coeff t k i) atTop (𝓝 ((U t).val k i)))
    (t : ℝ) (ht : 0 ≤ t) :
    SpectralReality (U t).val ∧ SpectralSolenoidal (U t).val ∧ SpectralMeanZero (U t).val := by
  refine ⟨?_, ?_, ?_⟩
  · intro k i
    have hleft := hc t ht (-k) i
    have hright := (hc t ht k i).star
    have heq : (fun n => (g n).coeff t (-k) i) =
        (fun n => star ((g n).coeff t k i)) := by
      funext n
      exact (g n).real_symmetry t ht k i
    rw [heq] at hleft
    exact tendsto_nhds_unique hleft hright
  · intro k
    have hsum : Tendsto (fun n => ∑ i : Fin 3, (k i : ℂ) * (g n).coeff t k i)
        atTop (𝓝 (∑ i : Fin 3, (k i : ℂ) * (U t).val k i)) := by
      apply tendsto_finset_sum
      intro i _
      exact (hc t ht k i).const_mul (k i : ℂ)
    have heq : (fun n => ∑ i : Fin 3, (k i : ℂ) * (g n).coeff t k i) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      exact (g n).solenoidal t ht k
    rw [heq] at hsum
    exact (tendsto_nhds_unique hsum tendsto_const_nhds)
  · intro i
    have hlim := hc t ht 0 i
    have heq : (fun n => (g n).coeff t 0 i) = (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      exact (g n).mode_support t ht 0 (cutoffModes_zero_not_mem _) i
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The modal limit has a genuine homogeneous-H1 Bochner representative and
inherits the ordinary integrated gradient bound. -/
theorem energy_modal_limit_H1_representative
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0)
    (hU : ∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0))
    (hc : ∀ t, 0 ≤ t → ∀ k i,
      Tendsto (fun n => (g n).coeff t k i) atTop (𝓝 ((U t).val k i))) :
    ∃ W : ℝ → CriticalSobolev 2,
      MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), criticalCoeff 2 (W t) = (U t).val) ∧
      (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ R ^ 2 / (2 * ν) := by
  apply critical_memLp_realization_of_modal_limit 2 T (R ^ 2 / (2 * ν))
    hT (by positivity) (fun n => (g n).criticalState 2) (fun t => (U t).val)
  · intro n
    exact ((g n).criticalState_continuousOn 2).mono (fun t ht => ht.1)
  · intro k i
    exact (hU k i).mono (fun t ht => ht.1)
  · intro t ht
    exact (energy_modal_limit_constraints ν a N g U hc t ht.1).2.2
  · intro n
    have heq (t : ℝ) : ‖(g n).criticalState 2 t‖ ^ 2 =
        coefficientDissipation (N n) ((g n).coeff t) := by
      rw [(g n).criticalState_norm_sq_nat 2 t, criticalEnergy_two_eq_coefficientDissipation]
    simp_rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).mpr
    have hE := (g n).coefficientEnergy_integral_identity hT
    have hE0 := hinit n
    have hEnonneg := coefficientEnergy_nonneg (N n) ((g n).coeff T)
    nlinarith
  · intro t ht k i
    simpa only [(g _).criticalState_coeff 2 ht.1] using hc t ht.1 k i

end
end QuasiFeffermanB

