import QuasiFeffermanB.Semantics

/-! Actual conservation of the constant test pairings and admissibility
of every positive-time L2 trace. No conservation axiom is assumed. -/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem physical_inner_congr_left_ae {v w : Field}
    (h : v =ᵐ[volume.restrict unitCube] w) (φ : Field) :
    physicalFieldInner v φ = physicalFieldInner w φ := by
  unfold physicalFieldInner
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem constant_positive_solenoidal_test (c : Vec) :
    CriticalPositiveSolenoidalTest (fun _ _ => c) := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · intro t ht x i
    rfl
  · intro t ht x
    simp [divergence, coordinateDerivative]

theorem constant_weak_momentum_integrand (ν : ℝ) (u : Velocity)
    (c : Vec) (t : ℝ) :
    criticalWeakMomentumIntegrand ν u (fun _ _ => c) t = 0 := by
  have hcoord (i : Fin 3) :
      coordinateDerivative (fun _ : Vec => c) i = fun _ => 0 := by
    funext x
    simp [coordinateDerivative]
  simp [criticalWeakMomentumIntegrand, physicalFieldInner, timeDerivative,
    laplacian, hcoord, criticalWeakTransport]

theorem LH_CONSTANT_PAIRING_PRESERVED
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity}
    {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) (c : Vec)
    (t : ℝ) (ht : 0 ≤ t) :
    physicalFieldInner (u t) (fun _ => c) =
      physicalFieldInner (a : Field) (fun _ => c) := by
  let f : ℝ → ℝ := fun r => physicalFieldInner (u r) (fun _ => c)
  have hpositive (r s : ℝ) (hr : 0 < r) (hs : 0 < s) : f r = f s := by
    rcases le_total r s with hrs | hsr
    · have h := hu.momentum.momentum (fun _ _ => c)
        (constant_positive_solenoidal_test c) r s hr hrs
      simp only [constant_weak_momentum_integrand, intervalIntegral.integral_zero] at h
      change f s - f r = 0 at h
      linarith
    · have h := hu.momentum.momentum (fun _ _ => c)
        (constant_positive_solenoidal_test c) s r hs hsr
      simp only [constant_weak_momentum_integrand, intervalIntegral.integral_zero] at h
      change f r - f s = 0 at h
      linarith
  have hinitial : f 0 = physicalFieldInner (a : Field) (fun _ => c) :=
    physical_inner_congr_left_ae hu.initial _
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    exact hinitial
  · have hc : MemLp (fun _ : Vec => c) 2 (volume.restrict unitCube) :=
      critical_continuous_memLp_cube _ continuous_const 2
    have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
      (hu.weak_continuity (fun _ => c) hc 0 (by simp)).mono Ioi_subset_Ici_self
    have heq : f =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => f t) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hpositive r t hr hpos
    have hconst : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f t)) :=
      tendsto_const_nhds.congr' heq.symm
    exact (tendsto_nhds_unique hconst hlim).trans hinitial

theorem LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity}
    {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) (ha : EnergySigmaZero a)
    (t : ℝ) (ht : 0 < t) :
    EnergySigmaZero (criticalL2Representative (u t)) := by
  have hL2 := hu.velocity_L2 t ht.le
  have hrep : (criticalL2Representative (u t) : Field)
      =ᵐ[volume.restrict unitCube] u t := by
    rw [criticalL2Representative_eq _ hL2]
    exact hL2.coeFn_toLp
  constructor
  · intro p hp hpp
    rw [physical_inner_congr_left_ae hrep]
    exact hu.momentum.gradient_annihilation t ht p hp hpp
  · intro i
    rw [physical_inner_congr_left_ae hrep,
      LH_CONSTANT_PAIRING_PRESERVED hu (unitVector i) t ht.le]
    exact ha.mean_zero i

end
end QuasiFeffermanB
