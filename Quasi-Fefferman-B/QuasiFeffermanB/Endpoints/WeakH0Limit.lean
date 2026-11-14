import QuasiFeffermanB.EnergyWeakContinuity
import QuasiFeffermanB.EnergyPhysicalContinuity
import QuasiFeffermanB.EnergyGalerkinCompactness
import SingularClosure.CriticalLimitUniform
import SingularClosure.CriticalWeakGradient

/-! QFB endpoint extraction R4. Bounded modal convergence implies convergence
against every physical L2 test. Candidate proof bodies; external compilation
and theorem-level axiom audit are pending. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem ENERGY_LP_WEAK_TENDSTO
    (F : ℕ → FourierVectorSequence) (v : FourierVectorSequence)
    (R : ℝ) (hR : 0 ≤ R) (hF : ∀ n, ‖F n‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hc : ∀ ki, Tendsto (fun n => F n ki) atTop (𝓝 (v ki)))
    (w : FourierVectorSequence) :
    Tendsto (fun n => inner ℂ (F n) w) atTop (𝓝 (inner ℂ v w)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hRp : 0 < R + 1 := by linarith
  have hδ : 0 < (ε / 4) / (R + 1) := div_pos (by positivity) hRp
  obtain ⟨S, hS⟩ :=
    (Metric.tendsto_nhds.mp (energy_lp_projection_tendsto w)
      ((ε / 4) / (R + 1)) hδ).exists
  have htail (z : FourierVectorSequence) (hz : ‖z‖ ≤ R) :
      dist (inner ℂ z (criticalLpProjection S w)) (inner ℂ z w) < ε / 4 := by
    have hnorm : ‖criticalLpProjection S w - w‖ < (ε / 4) / (R + 1) := by
      simpa only [dist_eq_norm] using hS
    calc
      dist (inner ℂ z (criticalLpProjection S w)) (inner ℂ z w)
          = ‖inner ℂ z (criticalLpProjection S w - w)‖ := by
            rw [dist_eq_norm, inner_sub_right]
      _ ≤ ‖z‖ * ‖criticalLpProjection S w - w‖ := norm_inner_le_norm _ _
      _ ≤ R * ‖criticalLpProjection S w - w‖ :=
        mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ (R + 1) * ‖criticalLpProjection S w - w‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < ε / 4 := by
        have h := (lt_div_iff₀ hRp).mp hnorm
        nlinarith
  have hfinite : Tendsto (fun n => inner ℂ (F n) (criticalLpProjection S w))
      atTop (𝓝 (inner ℂ v (criticalLpProjection S w))) := by
    simp_rw [energy_lp_inner_projection]
    exact tendsto_finset_sum S (fun ki _ => (hc ki).inner tendsto_const_nhds)
  filter_upwards [Metric.tendsto_nhds.mp hfinite (ε / 2) (by positivity)] with n hn
  have hleft :
      dist (inner ℂ (F n) w) (inner ℂ (F n) (criticalLpProjection S w)) < ε / 4 := by
    simpa only [dist_comm] using htail (F n) (hF n)
  have hright := htail v hv
  calc
    dist (inner ℂ (F n) w) (inner ℂ v w)
        ≤ dist (inner ℂ (F n) w) (inner ℂ (F n) (criticalLpProjection S w)) +
          (dist (inner ℂ (F n) (criticalLpProjection S w))
            (inner ℂ v (criticalLpProjection S w)) +
           dist (inner ℂ v (criticalLpProjection S w)) (inner ℂ v w)) :=
      (dist_triangle (inner ℂ (F n) w)
        (inner ℂ (F n) (criticalLpProjection S w)) (inner ℂ v w)).trans
          (add_le_add le_rfl
            (dist_triangle (inner ℂ (F n) (criticalLpProjection S w))
              (inner ℂ v (criticalLpProjection S w)) (inner ℂ v w)))
    _ < ε := by linarith

theorem ENERGY_H0_WEAK_TENDSTO
    (F : ℕ → TorusSobolev 0) (v : TorusSobolev 0)
    (R : ℝ) (hR : 0 ≤ R) (hF : ∀ n, ‖F n‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hc : ∀ k i, Tendsto (fun n => (F n).val k i) atTop (𝓝 (v.val k i)))
    (w : TorusSobolev 0) :
    Tendsto (fun n => inner ℂ (F n) w) atTop (𝓝 (inner ℂ v w)) := by
  have hb : ∀ n, ‖torusSobolevRepr 0 (F n)‖ ≤ R := by
    intro n
    simpa only [(torusSobolevRepr 0).norm_map] using hF n
  have hv' : ‖torusSobolevRepr 0 v‖ ≤ R := by
    simpa only [(torusSobolevRepr 0).norm_map] using hv
  have hc' : ∀ ki : FourierIndex,
      Tendsto (fun n => torusSobolevRepr 0 (F n) ki)
        atTop (𝓝 (torusSobolevRepr 0 v ki)) := by
    intro ki
    simpa only [torusSobolevRepr_apply, pow_zero, one_mul] using hc ki.1 ki.2
  have h := ENERGY_LP_WEAK_TENDSTO
    (fun n => torusSobolevRepr 0 (F n)) (torusSobolevRepr 0 v)
    R hR hb hv' hc' (torusSobolevRepr 0 w)
  simpa only [(torusSobolevRepr 0).inner_map_map] using h

theorem ENERGY_H0_LIMIT_NORM_LE
    (F : ℕ → TorusSobolev 0) (v : TorusSobolev 0) (R : ℝ)
    (hF : ∀ n, ‖F n‖ ≤ R)
    (hc : ∀ k i, Tendsto (fun n => (F n).val k i) atTop (𝓝 (v.val k i))) :
    ‖v‖ ≤ R := by
  have hcoeff (z : TorusSobolev 0) :
      criticalCoeff 0 (criticalH0Equiv.symm z) = z.val := by
    simpa only [criticalH0Equiv.apply_symm_apply] using
      (criticalH0Equiv_coeff (criticalH0Equiv.symm z)).symm
  obtain ⟨z, hz, hnorm⟩ := criticalSobolev_limit_mem_and_norm_le
    0 (fun n => criticalH0Equiv.symm (F n)) v.val R
    (fun n => by simpa only [criticalH0Equiv.symm.norm_map] using hF n)
    (by simpa only [hcoeff] using hc)
  have heq : criticalH0Equiv z = v := by
    apply Subtype.ext
    exact (criticalH0Equiv_coeff z).trans hz
  rw [← heq, criticalH0Equiv.norm_map]
  exact hnorm

local instance : InnerProductSpace ℝ (TorusSobolev 0) :=
  InnerProductSpace.rclikeToReal ℂ (TorusSobolev 0)

theorem ENERGY_PHYSICAL_L2_WEAK_TENDSTO
    (F : ℕ → TorusSobolev 0) (v : TorusSobolev 0)
    (R : ℝ) (hR : 0 ≤ R) (hF : ∀ n, ‖F n‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hc : ∀ k i, Tendsto (fun n => (F n).val k i) atTop (𝓝 (v.val k i)))
    (φ : PhysicalCubeL2) :
    Tendsto (fun n => inner ℝ (energyH0PhysicalMap (F n)) φ)
      atTop (𝓝 (inner ℝ (energyH0PhysicalMap v) φ)) := by
  have h := ENERGY_H0_WEAK_TENDSTO F v R hR hF hv hc
    (energyH0PhysicalMap.adjoint φ)
  have hr : Tendsto
      (fun n => inner ℝ (F n) (energyH0PhysicalMap.adjoint φ))
      atTop (𝓝 (inner ℝ v (energyH0PhysicalMap.adjoint φ))) := by
    change Tendsto
      (fun n => Complex.re (inner ℂ (F n) (energyH0PhysicalMap.adjoint φ)))
      atTop (𝓝 (Complex.re (inner ℂ v (energyH0PhysicalMap.adjoint φ))))
    exact Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hr

theorem energy_galerkin_physical_L2
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (r : ℝ) (hr : 0 ≤ r) :
    criticalL2Representative (g.velocity r) =
      energyH0PhysicalMap (g.sobolevState 0 r) := by
  have hv : MemLp (g.velocity r) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (finiteSynthesis_contDiff N (g.coeff r)).continuous 2
  have hre : SpectralReality (g.sobolevState 0 r).val := by
    rw [g.sobolevState_coeff 0 hr]
    exact g.real_symmetry r hr
  have hz : SpectralMeanZero (g.sobolevState 0 r).val := by
    rw [g.sobolevState_coeff 0 hr]
    intro i
    exact g.mode_support r hr 0 (cutoffModes_zero_not_mem N) i
  apply physicalL2_fourier_injective
  rw [criticalL2Representative_eq _ hv,
    criticalCube_datumFourierCoeff_congr_ae hv.coeFn_toLp]
  change datumFourierCoeff (finiteSynthesis N (g.coeff r)) =
    datumFourierCoeff (torusToPhysicalCubeL2 (torusSobolevL2 (g.sobolevState 0 r)) : Field)
  rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N (g.coeff r)
      (g.real_symmetry r hr),
    torusSobolevH0_physical_fourierCoeff _ hre hz, g.sobolevState_coeff 0 hr]
  exact g.cutoffCoeff_eq r hr

theorem ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R : ℝ) (hR : 0 ≤ R)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0)
    (hc : ∀ t, 0 ≤ t → ∀ k i,
      Tendsto (fun n => (g n).coeff t k i) atTop (𝓝 ((U t).val k i)))
    (r : ℝ) (hr : 0 ≤ r) (φ : Field)
    (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    Tendsto (fun n => physicalFieldInner ((g n).velocity r) φ)
      atTop (𝓝 (physicalFieldInner (energyPeriodicVelocity U r) φ)) := by
  let F : ℕ → TorusSobolev 0 := fun n => (g n).sobolevState 0 r
  have hF : ∀ n, ‖F n‖ ≤ R :=
    fun n => galerkin_H0_energy_bound hν (g n) R hR (hinit n) r hr
  have hcoeff : ∀ k i,
      Tendsto (fun n => (F n).val k i) atTop (𝓝 ((U r).val k i)) := by
    have heq (n : ℕ) : (F n).val = (g n).coeff r :=
      (g n).sobolevState_coeff 0 hr
    simpa only [heq] using hc r hr
  have hU := ENERGY_H0_LIMIT_NORM_LE F (U r) R hF hcoeff
  have h := ENERGY_PHYSICAL_L2_WEAK_TENDSTO F (U r) R hR hF hU hcoeff
    (criticalL2Representative φ)
  have hn (n : ℕ) : inner ℝ (energyH0PhysicalMap (F n))
      (criticalL2Representative φ) = physicalFieldInner ((g n).velocity r) φ := by
    have hv : MemLp ((g n).velocity r) 2 (volume.restrict unitCube) :=
      critical_continuous_memLp_cube _
        (finiteSynthesis_contDiff (N n) ((g n).coeff r)).continuous 2
    change inner ℝ (energyH0PhysicalMap ((g n).sobolevState 0 r))
      (criticalL2Representative φ) = _
    rw [← energy_galerkin_physical_L2 (g n) r hr,
      criticalL2Representative_eq _ hv, criticalL2Representative_eq _ hφ]
    exact (critical_physicalFieldInner_eq_L2_inner _ _ hv hφ).symm
  have hu : inner ℝ (energyH0PhysicalMap (U r)) (criticalL2Representative φ) =
      physicalFieldInner (energyPeriodicVelocity U r) φ := by
    have hv := energyPeriodicVelocity_memLp U r
    rw [energyH0PhysicalMap_apply U r, ← energyPeriodicVelocity_L2 U r,
      criticalL2Representative_eq _ hv, criticalL2Representative_eq _ hφ]
    exact (critical_physicalFieldInner_eq_L2_inner _ _ hv hφ).symm
  simpa only [hn, hu] using h

end
end QuasiFeffermanB
