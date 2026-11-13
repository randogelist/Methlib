import QuasiFeffermanB.EnergyGlobalPhysical

/-! Literal periodic representatives for the energy-class Fourier limit.
The choice of an Lp representative on the physical cube alone does not imply
pointwise periodicity. The explicit quotient pullback below supplies it. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_cubeTorusMap_periodic : SpatialPeriodic criticalCubeTorusMap := by
  intro x i
  funext j
  have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
    exact ⟨1, by simp⟩
  change (((x + unitVector i) j : ℝ) : UnitAddCircle) = (x j : UnitAddCircle)
  by_cases hij : j = i
  · subst j
    simp [PiLp.add_apply, unitVector, AddCircle.coe_add, hone]
  · simp [PiLp.add_apply, unitVector, hij, Ne.symm hij]

def energyPeriodicField (c : TorusSobolev 0) : Field :=
  fun x => WithLp.toLp 2
    (fun i : Fin 3 => ((torusSobolevL2 c) i (criticalCubeTorusMap x)).re)

theorem energyPeriodicField_periodic (c : TorusSobolev 0) :
    SpatialPeriodic (energyPeriodicField c) := by
  intro x i
  simp only [energyPeriodicField, energy_cubeTorusMap_periodic x i]

theorem energyPeriodicField_coe (c : TorusSobolev 0) :
    (torusToPhysicalCubeL2 (torusSobolevL2 c) : Field)
      =ᵐ[volume.restrict unitCube] energyPeriodicField c := by
  let F : Fin 3 → PhysicalCubeL2 := fun i =>
    (criticalRealCoordinate i).compLpL 2 (volume.restrict unitCube)
      (criticalScalarCubePullback ((torusSobolevL2 c) i))
  have hF (i : Fin 3) : F i =ᵐ[volume.restrict unitCube]
      (fun x => ((torusSobolevL2 c) i (criticalCubeTorusMap x)).re • unitVector i) := by
    have hc := (criticalRealCoordinate i).coeFn_compLpL
      (criticalScalarCubePullback ((torusSobolevL2 c) i))
    have hp := Lp.coeFn_compMeasurePreserving ((torusSobolevL2 c) i)
      criticalCubeTorusMap_measurePreserving
    filter_upwards [hc, hp] with x hx hy
    change F i x = _
    simp only [Function.comp_apply] at hy
    change criticalScalarCubePullback ((torusSobolevL2 c) i) x =
      (torusSobolevL2 c) i (criticalCubeTorusMap x) at hy
    rw [hx, hy]
    rfl
  have hall : ∀ᵐ x ∂volume.restrict unitCube, ∀ i : Fin 3,
      F i x = ((torusSobolevL2 c) i (criticalCubeTorusMap x)).re • unitVector i :=
    ae_all_iff.mpr hF
  have heq : torusToPhysicalCubeL2 (torusSobolevL2 c) = ∑ i : Fin 3, F i := by
    simp only [torusToPhysicalCubeL2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, F]
    rfl
  rw [heq]
  filter_upwards [critical_Lp_sum_coe Finset.univ F, hall] with x hx hy
  rw [hx]
  simp_rw [hy]
  exact sum_coordinate_unitVector (energyPeriodicField c x)

def energyPeriodicVelocity (U : ℝ → TorusSobolev 0) : Velocity :=
  fun t => energyPeriodicField (U t)

theorem energyPeriodicVelocity_ae (U : ℝ → TorusSobolev 0) (t : ℝ) :
    energyPhysicalVelocity U t =ᵐ[volume.restrict unitCube] energyPeriodicVelocity U t :=
  energyPeriodicField_coe (U t)

theorem energyPeriodicVelocity_memLp (U : ℝ → TorusSobolev 0) (t : ℝ) :
    MemLp (energyPeriodicVelocity U t) 2 (volume.restrict unitCube) :=
  (memLp_congr_ae (energyPeriodicVelocity_ae U t)).mp
    (Lp.memLp (energyPhysicalVelocityL2 U t))

theorem energyPeriodicVelocity_L2 (U : ℝ → TorusSobolev 0) (t : ℝ) :
    criticalL2Representative (energyPeriodicVelocity U t) = energyPhysicalVelocityL2 U t := by
  rw [criticalL2Representative_eq _ (energyPeriodicVelocity_memLp U t)]
  apply Lp.ext
  exact (energyPeriodicVelocity_memLp U t).coeFn_toLp.trans (energyPeriodicVelocity_ae U t).symm

theorem energyPeriodicField_fourierCoeff (c : TorusSobolev 0)
    (hr : SpectralReality c.val) (hz : SpectralMeanZero c.val) :
    datumFourierCoeff (energyPeriodicField c) = c.val := by
  rw [← criticalCube_datumFourierCoeff_congr_ae (energyPeriodicField_coe c)]
  exact torusSobolevH0_physical_fourierCoeff c hr hz

theorem energyPeriodicField_gradient_annihilation (c : TorusSobolev 0)
    (hr : SpectralReality c.val) (hs : SpectralSolenoidal c.val)
    (hz : SpectralMeanZero c.val) (p : Vec → ℝ)
    (hp : ContDiff ℝ ∞ p) (hpp : SpatialPeriodic p) :
    physicalFieldInner (energyPeriodicField c) (SingularClosure.gradient p) = 0 := by
  have hv : MemLp (energyPeriodicField c) 2 (volume.restrict unitCube) :=
    (memLp_congr_ae (energyPeriodicField_coe c)).mp
      (Lp.memLp (torusToPhysicalCubeL2 (torusSobolevL2 c)))
  have hc := energyPeriodicField_fourierCoeff c hr hz
  have hcut := physicalL2_cutoff_eLpNorm_tendsto (energyPeriodicField c) hv
    (by rw [hc]; exact hz)
  have hconv : Tendsto
      (fun N => physicalFieldInner (finiteSynthesis N c.val) (SingularClosure.gradient p))
      atTop (𝓝 (physicalFieldInner (energyPeriodicField c) (SingularClosure.gradient p))) := by
    apply critical_physicalFieldInner_tendsto
      (fun N => finiteSynthesis N c.val) (energyPeriodicField c) (SingularClosure.gradient p)
      (fun N => critical_continuous_memLp_cube _ (finiteSynthesis_contDiff N _).continuous 2)
      hv (critical_continuous_memLp_cube _ (criticalWeak_gradient_continuous p hp) 2)
    simpa only [hc] using hcut
  have hzero (N : ℕ) : physicalFieldInner (finiteSynthesis N c.val) (SingularClosure.gradient p) = 0 :=
    critical_smooth_integral_inner_gradient_eq_zero _ p (finiteSynthesis_contDiff N _)
      hp (finiteSynthesis_periodic N _) hpp (finiteSynthesis_divergence_free N _ hs)
  have hzeroLim : Tendsto
      (fun N => physicalFieldInner (finiteSynthesis N c.val) (SingularClosure.gradient p)) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hconv hzeroLim

theorem energy_physicalH1_congr_velocity {v w : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (h : CriticalPhysicalH1 v G) (heq : v =ᵐ[volume.restrict unitCube] w) :
    CriticalPhysicalH1 w G := by
  obtain ⟨z, hz, hzp, hzv, hzG⟩ := h.approximation
  refine ⟨(memLp_congr_ae heq).mp h.velocity_L2,
    h.derivative_L2, ⟨z, hz, hzp, ?_, hzG⟩⟩
  have hnorm (n : ℕ) : eLpNorm (z n - w) 2 (volume.restrict unitCube) =
      eLpNorm (z n - v) 2 (volume.restrict unitCube) :=
    eLpNorm_congr_ae (Filter.EventuallyEq.sub Filter.EventuallyEq.rfl heq.symm)
  simpa only [hnorm] using hzv

theorem energyPeriodicVelocity_spatial_H1 (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hr : ∀ᵐ t ∂μ, SpectralReality (U t).val)
    (hz : ∀ᵐ t ∂μ, SpectralMeanZero (U t).val)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    ∀ᵐ t ∂μ, CriticalPhysicalH1 (energyPeriodicVelocity U t) (energyGlobalGradient U t) := by
  filter_upwards [energyGlobalPhysical_spatial_H1 U W μ hr hz hw] with t ht
  exact energy_physicalH1_congr_velocity ht (energyPeriodicVelocity_ae U t)

end
end QuasiFeffermanB
