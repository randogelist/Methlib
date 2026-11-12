import QuasiFeffermanB.CaloricCompactness
import QuasiFeffermanB.CaloricAdmission
import SingularClosure.CriticalSerrinTime
import SingularClosure.CriticalCubeL2

/-! Physical trace, gradient bound and Serrin control for a datumwise
caloric flow. No monotonicity of its critical norm is assumed. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal ContDiff

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem POSITIVE_FLOW_PHYSICAL_L2_OF_CRITICAL_COEFFICIENTS
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (u : ℝ → CriticalSobolev 1)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (t : ℝ) (ht : 0 < t) :
    criticalInitialPhysicalL2 (u t) = physicalFieldL2 (L.velocity t)
      (L.velocity_smoothSigmaZero t ht).smooth.continuous := by
  have hs := L.velocity_smoothSigmaZero t ht
  have hc : criticalPhysicalL2 1 (by norm_num) (u t) =
      torusPhysicalFieldL2 (L.velocity t) hs.smooth.continuous := by
    apply torusVectorFourierCoeff_injective
    rw [criticalPhysicalL2_fourierCoeff, torusPhysicalFieldL2_fourierCoeff]
    change criticalCoeff 1 (u t) = datumFourierCoeff
      (smoothFourierSynthesis (L.state 0 t).val)
    rw [datumFourierCoeff_smoothFourierSynthesis _
      (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (L.state_all_mem t ht)) (L.reality t ht)]
    exact (hL t ht).symm
  change torusToPhysicalCubeL2 (criticalPhysicalL2 1 (by norm_num) (u t)) = _
  rw [hc]
  exact torusToPhysicalCubeL2_physicalField _ hs.smooth.continuous hs.periodic

theorem POSITIVE_FLOW_STRONG_PHYSICAL_TRACE_OF_CRITICAL_CURVE
    {ν : ℝ} (a : CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (u : ℝ → CriticalSobolev 1) (hu : ContinuousOn u (Ici (0 : ℝ)))
    (hzero : u 0 = a)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t)) :
    Tendsto (fun t => eLpNorm
      (L.velocity t - (criticalInitialPhysicalL2 a : Field)) 2
      (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let U : ℝ → PhysicalCubeL2 := fun t => criticalInitialPhysicalL2 (u t)
  have hc : ContinuousOn U (Ici 0) :=
    torusToPhysicalCubeL2.continuous.comp_continuousOn
      ((criticalPhysicalL2 1 (by norm_num)).continuous.comp_continuousOn hu)
  have ht : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (criticalInitialPhysicalL2 a)) := by
    have h := (hc 0 (by exact le_rfl)).mono
      (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
    simpa only [U, hzero] using h
  have h := (ht.sub_const (criticalInitialPhysicalL2 a)).enorm
  have h0 : Tendsto (fun t => ‖U t - criticalInitialPhysicalL2 a‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [sub_self, enorm_zero] using h
  apply h0.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hfield : U t =ᵐ[volume.restrict unitCube] L.velocity t := by
    change (criticalInitialPhysicalL2 (u t) : Field) =ᵐ[_] _
    rw [POSITIVE_FLOW_PHYSICAL_L2_OF_CRITICAL_COEFFICIENTS L u hL t ht]
    exact physicalFieldL2_coe _ _
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact (Lp.coeFn_sub _ _).trans (hfield.sub Filter.EventuallyEq.rfl)

theorem POSITIVE_FLOW_PHYSICAL_ENERGY_OF_CRITICAL_BOUND
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (u : ℝ → CriticalSobolev 1)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (A : ℝ) (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ A)
    (t : ℝ) (ht : 0 < t) : physicalEnergy (L.velocity t) ≤ A ^ 2 := by
  let w : CriticalSobolev 0 := criticalSobolevLower 0 1 (by norm_num) (u t)
  have hw : criticalCoeff 0 w = (L.state 0 t).val := by
    rw [criticalSobolevLower_coeff, hL t ht]
  have heq := critical_smoothFourierSynthesis_energy_eq_norm_sq
    (L.state 0 t).val (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (L.state_all_mem t ht))
    (L.reality t ht) w hw
  change physicalEnergy (L.velocity t) = ‖w‖ ^ 2 at heq
  rw [heq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((criticalSobolevLower_norm_le 0 1 (by norm_num) (u t)).trans (hbound t ht.le)) 2

theorem POSITIVE_FLOW_DISSIPATION_OF_GALERKIN_BOUND
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ)
    (g : ∀ n : ℕ, GalerkinSolution ν (a n) (φ n + 1))
    (L : CriticalPositiveSobolevFlow ν) (D : ℝ) (hD : 0 ≤ D)
    (u : ℝ → TorusSobolev 0)
    (hL : ∀ t : ℝ, 0 < t → L.state 0 t = u t)
    (hbound : ∀ n t, 0 ≤ t → coefficientDissipation (φ n + 1) ((g n).coeff t) ≤ D)
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u
      atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : 0 < t) : physicalDissipation (L.velocity t) ≤ D := by
  have hcoeff (k : Frequency) (i : Fin 3) : Tendsto
      (fun n => criticalCoeff 2 ((g n).criticalState 2 t) k i) atTop
      (𝓝 ((L.state 0 t).val k i)) := by
    rw [hL t ht]
    exact criticalGalerkinLimit_criticalState_coeff_tendsto ν a φ g
      u t (hconv t ht) 2 t ⟨ht.le, le_rfl⟩ k i
  have hlow := criticalExtendedSquare_le_liminf 2
    (fun n => (g n).criticalState 2 t) (L.state 0 t).val hcoeff
  have hlim : atTop.liminf (fun n => ENNReal.ofReal (‖(g n).criticalState 2 t‖ ^ 2)) ≤
      ENNReal.ofReal D := by
    apply liminf_le_of_frequently_le'
    apply Filter.Frequently.of_forall
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [show ‖(g n).criticalState 2 t‖ ^ 2 = criticalEnergy 2 (φ n + 1) ((g n).coeff t)
      from (g n).criticalState_norm_sq_nat 2 t,
      criticalEnergy_two_eq_coefficientDissipation]
    exact hbound n t ht.le
  rw [critical_smooth_extendedSquare_eq_dissipation _ (L.state_all_mem t ht)
    (L.reality t ht) (L.mean_zero t ht)] at hlow
  exact (ENNReal.ofReal_le_ofReal_iff hD).mp (hlow.trans hlim)

theorem POSITIVE_FLOW_SERRIN_OF_UNIFORM_PHYSICAL_BOUNDS
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (E D : ℝ)
    (hE : ∀ t : ℝ, 0 < t → physicalEnergy (L.velocity t) ≤ E)
    (hD : ∀ t : ℝ, 0 < t → physicalDissipation (L.velocity t) ≤ D)
    (T : ℝ) :
    MemLp (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have hm : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (L.velocity t)) μ :=
    criticalPositive_spatialNorm_six_aestronglyMeasurable L T
  obtain ⟨K, hK, hb⟩ := CRITICAL_SMOOTH_L6_FOURTH_BOUND
  have hi : Integrable (fun _ : ℝ => K * (9 * D ^ 2 + E ^ 2)) μ := integrable_const _
  have hfour : Integrable (fun t => criticalSpatialNorm 6 (L.velocity t) ^ 4) μ := by
    apply hi.mono' (hm.pow 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (pow_nonneg (criticalSpatialNorm_nonneg 6 _) 4)]
    have hE0 : 0 ≤ physicalEnergy (L.velocity t) := by
      rw [physicalEnergy_eq_integral_norm_sq]
      exact integral_nonneg (fun x => sq_nonneg _)
    have hD0 : 0 ≤ physicalDissipation (L.velocity t) :=
      integral_nonneg (gradientSquareDensity_nonneg (L.velocity t))
    apply (hb _ (L.velocity_smoothSigmaZero t ht.1).smooth
      (L.velocity_smoothSigmaZero t ht.1).periodic).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 (hD t ht.1) 2)
      (by norm_num)) (pow_le_pow_left₀ hE0 (hE t ht.1) 2)
  apply (integrable_norm_rpow_iff hm
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp
  have hnorm (t : ℝ) : ‖criticalSpatialNorm 6 (L.velocity t)‖ = criticalSpatialNorm 6 (L.velocity t) :=
    Real.norm_of_nonneg (criticalSpatialNorm_nonneg 6 _)
  have hpow (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_ofNat x 4
  simpa only [ENNReal.toReal_ofNat, hnorm, hpow] using hfour

end
end QuasiFeffermanB
