import QuasiFeffermanB.EnergyFiniteWeakPairing
import QuasiFeffermanB.SpatialAdmission
import SingularClosure.CriticalGalerkin
import SingularClosure.SmoothFourierLaplacian

/-!
# Exact finite Galerkin pairing and time-dependent testing

Status: A_TIER_CANDIDATE.  These proof bodies have not been elaborated by the
external compiler.  The cached baseline run does not certify this module.

QFB: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c.
Foundation: 09dfe94a1ef150e21d09df3013fbe09002ef139c.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

The finite velocity requires only the literal coefficient ODE and continuity.
The physical test need not have zero mean.  Projection is removed from the
linear pairings, while the transport retains the actual finite projection.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff Interval

namespace QuasiFeffermanB

open SingularClosure

noncomputable section

/-- Coordinate continuity of the coefficient family gives joint continuity
of its finite physical synthesis. -/
theorem energy_finiteSynthesis_joint_continuousOn
    (N : ℕ) (c : ℝ → FourierCoeff) (I : Set ℝ)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ContinuousOn (fun r => c r k i) I) :
    ContinuousOn (fun z : ℝ × Vec => finiteSynthesis N (c z.1) z.2)
      {z | z.1 ∈ I} := by
  classical
  simp_rw [finiteSynthesis_eq_sum_unitVector]
  apply continuousOn_finset_sum
  intro i _
  have hscalar : ContinuousOn
      (fun z : ℝ × Vec =>
        (∑ k ∈ cutoffModes N, fourierCharacter k z.2 * c z.1 k i).re)
      {z | z.1 ∈ I} := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_finset_sum
    intro k _
    exact ((fourierCharacter_contDiff k).continuous.comp continuous_snd).continuousOn.mul
      ((hc k i).comp continuous_fst.continuousOn (fun z hz => hz))
  have hunit : ContinuousOn (fun _ : ℝ × Vec => (unitVector i : Vec))
      {z | z.1 ∈ I} := continuousOn_const
  intro z hz
  exact Filter.Tendsto.smul (hscalar z hz) (hunit z hz)

/-- The actual finite NSE vector field preserves coordinate continuity.
Every denominator in the Leray multiplier is a constant in time. -/
theorem energy_galerkinRhs_coordinate_continuousOn
    (ν : ℝ) (N : ℕ) (c : ℝ → FourierCoeff) (I : Set ℝ)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ContinuousOn (fun r => c r k i) I)
    (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun r => galerkinRhs ν N (c r) k i) I := by
  classical
  have htransport (l : Fin 3) :
      ContinuousOn (fun r => coefficientTransport N (c r) k l) I := by
    unfold coefficientTransport
    apply continuousOn_finset_sum
    intro p _
    apply ContinuousOn.mul _ (hc (k - p) l)
    apply continuousOn_finset_sum
    intro j _
    exact (hc p j).mul continuousOn_const
  have hleray : ContinuousOn
      (fun r => coefficientLeray k (coefficientTransport N (c r) k) i) I := by
    by_cases hk : k = 0
    · simpa only [coefficientLeray, if_pos hk] using htransport i
    · simp only [coefficientLeray, if_neg hk, div_eq_mul_inv]
      apply ContinuousOn.sub (htransport i)
      apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      apply continuousOn_finset_sum
      intro j _
      exact continuousOn_const.mul (htransport j)
  exact (continuousOn_const.mul (hc k i)).sub hleray

/-- Joint positive-time continuity of the finite velocity. -/
theorem energyGalerkin_velocity_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun z : ℝ × Vec => g.velocity z.1 z.2) {z | 0 < z.1} := by
  have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := Ioi_subset_Ici_self
  exact energy_finiteSynthesis_joint_continuousOn N g.coeff (Ioi 0)
    (fun k i => (g.coefficient_continuous k i).mono hsub)

/-- Joint positive-time continuity of the literal within-`Ici 0` derivative. -/
theorem energyGalerkin_timeDerivative_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun z : ℝ × Vec => timeDerivative g.velocity z.1 z.2)
      {z | 0 < z.1} := by
  have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := Ioi_subset_Ici_self
  have hcoeff : ∀ k : Frequency, ∀ i : Fin 3,
      ContinuousOn (fun r => g.coeff r k i) (Ioi 0) :=
    fun k i => (g.coefficient_continuous k i).mono hsub
  have h := energy_finiteSynthesis_joint_continuousOn N
    (fun r => galerkinRhs ν N (g.coeff r)) (Ioi 0)
    (energy_galerkinRhs_coordinate_continuousOn ν N g.coeff (Ioi 0) hcoeff)
  apply h.congr
  intro z hz
  exact congrArg (fun f : Field => f z.2)
    (g.timeDerivative_eq_finiteSynthesis z.1 hz.le)

/-- At positive time the literal Galerkin derivative is an ordinary derivative. -/
theorem energyGalerkin_velocity_hasDerivAt
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 < t) (x : Vec) :
    HasDerivAt (fun r => g.velocity r x) (timeDerivative g.velocity t x) t := by
  rw [g.timeDerivative_eq_finiteSynthesis t ht.le]
  exact (g.velocity_hasDerivWithinAt t ht.le x).hasDerivAt (Ici_mem_nhds ht)

/-- A separate opaque proof of the physical product rule keeps integral
elaboration independent of the finite Galerkin representation. -/
private theorem energy_physical_pairing_hasDerivAt_of_joint
    (u du v dv : Velocity)
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) {z | 0 < z.1})
    (hdu : ContinuousOn (fun z : ℝ × Vec => du z.1 z.2) {z | 0 < z.1})
    (hv : ContinuousOn (fun z : ℝ × Vec => v z.1 z.2) {z | 0 < z.1})
    (hdv : ContinuousOn (fun z : ℝ × Vec => dv z.1 z.2) {z | 0 < z.1})
    (hud : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      HasDerivAt (fun q => u q x) (du r x) r)
    (hvd : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      HasDerivAt (fun q => v q x) (dv r x) r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalFieldInner (u r) (v r))
      (physicalFieldInner (u t) (dv t) + physicalFieldInner (du t) (v t)) t := by
  let F : ℝ → Vec → ℝ := fun r x => inner ℝ (u r x) (v r x)
  let D : ℝ → Vec → ℝ := fun r x =>
    inner ℝ (u r x) (dv r x) + inner ℝ (du r x) (v r x)
  have hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) {z | 0 < z.1} :=
    hu.inner hv
  have hD : ContinuousOn (fun z : ℝ × Vec => D z.1 z.2) {z | 0 < z.1} :=
    (hu.inner hdv).add (hdu.inner hv)
  have hd : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      HasDerivAt (fun q => F q x) (D r x) r := by
    intro r hr x
    change HasDerivAt (fun q => inner ℝ (u q x) (v q x))
      (inner ℝ (u r x) (dv r x) + inner ℝ (du r x) (v r x)) r
    exact (hud r hr x).inner ℝ (hvd r hr x)
  have hIntegral : HasDerivAt (fun r => ∫ x in unitCube, F r x)
      (∫ x in unitCube, D t x) t :=
    critical_hasDerivAt_real_cube_integral F D hF hD hd t ht
  have huc : Continuous (u t) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hduc : Continuous (du t) :=
    hdu.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hvc : Continuous (v t) :=
    hv.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hdvc : Continuous (dv t) :=
    hdv.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hI₁ : IntegrableOn (fun x => inner ℝ (u t x) (dv t x)) unitCube volume :=
    physicalFieldInner_integrable (u t) (dv t) huc hdvc
  have hI₂ : IntegrableOn (fun x => inner ℝ (du t x) (v t x)) unitCube volume :=
    physicalFieldInner_integrable (du t) (v t) hduc hvc
  have hDIntegral : (∫ x in unitCube, D t x) =
      physicalFieldInner (u t) (dv t) + physicalFieldInner (du t) (v t) := by
    change (∫ x in unitCube, inner ℝ (u t x) (dv t x) + inner ℝ (du t x) (v t x)) =
      (∫ x in unitCube, inner ℝ (u t x) (dv t x)) +
        (∫ x in unitCube, inner ℝ (du t x) (v t x))
    exact integral_add hI₁ hI₂
  rw [hDIntegral] at hIntegral
  exact hIntegral

/-- Differentiation of the actual physical pairing, without a smoothness
bootstrap for the Galerkin trajectory. -/
theorem ENERGY_GALERKIN_PAIRING_HASDERIV
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => physicalFieldInner (g.velocity r) (φ r))
      (physicalFieldInner (g.velocity t) (timeDerivative φ t) +
       physicalFieldInner (timeDerivative g.velocity t) (φ t)) t := by
  exact energy_physical_pairing_hasDerivAt_of_joint
    g.velocity (timeDerivative g.velocity) φ (timeDerivative φ)
    (energyGalerkin_velocity_continuousOn g)
    (energyGalerkin_timeDerivative_continuousOn g)
    hφ.smooth.continuousOn hφ.timeDerivative_continuousOn
    (energyGalerkin_velocity_hasDerivAt g) hφ.time_hasDerivAt t ht

/-- Finite synthesis pairs with the Fourier projection of a continuous real
field exactly as it pairs with the original field.  No mean-zero hypothesis
on the second field is used. -/
theorem energy_finite_projection_pairing
    (N : ℕ) (c : FourierCoeff) (f : Field) (hf : Continuous f) :
    physicalFieldInner (finiteSynthesis N c)
      (finiteSynthesis N (datumFourierCoeff f)) =
    physicalFieldInner (finiteSynthesis N c) f := by
  unfold physicalFieldInner
  rw [integral_finiteSynthesis_pairing N c _
    (finiteSynthesis_contDiff N (datumFourierCoeff f)).continuous,
    integral_finiteSynthesis_pairing N c f hf,
    criticalGalerkin_datumFourierCoeff_finiteSynthesis N (datumFourierCoeff f)
      (datumFourierCoeff_reality f)]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i _
  rw [cutoffCoeff_apply_of_mem (datumFourierCoeff f) hk i]

/-- The literal physical Laplacian commutes with the finite Fourier projection. -/
theorem energy_test_projection_laplacian
    (N : ℕ) (f : Field) (hf : ContDiff ℝ ∞ f) (hfp : SpatialPeriodic f) :
    laplacian (finiteSynthesis N (datumFourierCoeff f)) =
      finiteSynthesis N (datumFourierCoeff (laplacian f)) := by
  rw [finiteSynthesis_laplacian, datumFourierCoeff_laplacian f hf hfp]

/-- Fourier solenoidality follows from the actual smooth physical test. -/
theorem energyTest_fourier_solenoidal
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ) (t : ℝ) (ht : 0 < t) :
    SpectralSolenoidal (datumFourierCoeff (φ t)) := by
  apply physical_gradient_annihilation_fourier_solenoidal (φ t)
    (critical_continuous_memLp_cube (φ t) (hφ.spatial_smooth ht).continuous 2)
  intro p hp hpp
  exact critical_smooth_integral_inner_gradient_eq_zero (φ t) p
    (hφ.spatial_smooth ht) hp (hφ.periodic t ht) hpp (hφ.solenoidal t ht)

/-- The exact finite weak equation tested against the original field in both
linear terms; only the nonlinear test retains the cutoff. -/
theorem energyGalerkin_projected_test_pairing
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ) (t : ℝ) (ht : 0 < t) :
    physicalFieldInner (timeDerivative g.velocity t) (φ t) =
      ν * physicalFieldInner (g.velocity t) (laplacian (φ t)) +
        criticalWeakTransport (g.velocity t)
          (finiteSynthesis N (datumFourierCoeff (φ t))) := by
  have h := energyGalerkin_finite_test_pairing g (datumFourierCoeff (φ t))
    (datumFourierCoeff_reality (φ t)) (energyTest_fourier_solenoidal φ hφ t ht) t ht.le
  have htime : physicalFieldInner (timeDerivative g.velocity t)
      (finiteSynthesis N (datumFourierCoeff (φ t))) =
        physicalFieldInner (timeDerivative g.velocity t) (φ t) := by
    rw [g.timeDerivative_eq_finiteSynthesis t ht.le]
    exact energy_finite_projection_pairing N (galerkinRhs ν N (g.coeff t))
      (φ t) (hφ.spatial_smooth ht).continuous
  have hlap : physicalFieldInner (g.velocity t)
      (laplacian (finiteSynthesis N (datumFourierCoeff (φ t)))) =
        physicalFieldInner (g.velocity t) (laplacian (φ t)) := by
    rw [energy_test_projection_laplacian N (φ t)
      (hφ.spatial_smooth ht) (hφ.periodic t ht)]
    exact energy_finite_projection_pairing N (g.coeff t) (laplacian (φ t))
      (laplacian_contDiff (φ t) (hφ.spatial_smooth ht)).continuous
  rw [htime, hlap] at h
  exact h

/-- Separate time integrability of precisely the three finite-test terms.
The projected transport is continuous by its exact finite weak pairing. -/
theorem ENERGY_GALERKIN_TIME_TEST_INTEGRABLE
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable
      (fun r => physicalFieldInner (g.velocity r) (timeDerivative φ r)) volume s t ∧
    IntervalIntegrable
      (fun r => physicalFieldInner (g.velocity r) (laplacian (φ r))) volume s t ∧
    IntervalIntegrable
      (fun r => criticalWeakTransport (g.velocity r)
        (finiteSynthesis N (datumFourierCoeff (φ r)))) volume s t := by
  have hg := energyGalerkin_velocity_continuousOn g
  have hgt := energyGalerkin_timeDerivative_continuousOn g
  have htime : ContinuousOn
      (fun r => physicalFieldInner (g.velocity r) (timeDerivative φ r)) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (g.velocity r x) (timeDerivative φ r x))
      (hg.inner hφ.timeDerivative_continuousOn) s t hs
  have hlap : ContinuousOn
      (fun r => physicalFieldInner (g.velocity r) (laplacian (φ r))) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (g.velocity r x) (laplacian (φ r) x))
      (hg.inner hφ.laplacian_continuousOn) s t hs
  have hderiv : ContinuousOn
      (fun r => physicalFieldInner (timeDerivative g.velocity r) (φ r)) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (timeDerivative g.velocity r x) (φ r x))
      (hgt.inner hφ.smooth.continuousOn) s t hs
  have htransport : ContinuousOn
      (fun r => criticalWeakTransport (g.velocity r)
        (finiteSynthesis N (datumFourierCoeff (φ r)))) (Icc s t) := by
    apply (hderiv.sub (hlap.const_mul ν)).congr
    intro r hr
    have he := energyGalerkin_projected_test_pairing g φ hφ r (hs.trans_le hr.1)
    change criticalWeakTransport (g.velocity r)
        (finiteSynthesis N (datumFourierCoeff (φ r))) =
      physicalFieldInner (timeDerivative g.velocity r) (φ r) -
        ν * physicalFieldInner (g.velocity r) (laplacian (φ r))
    rw [he]
    ring
  exact ⟨htime.intervalIntegrable_of_Icc hst,
    hlap.intervalIntegrable_of_Icc hst, htransport.intervalIntegrable_of_Icc hst⟩

/-- The exact finite time-dependent test identity on an arbitrary positive
closed slab.  Endpoint and linear test terms are unprojected. -/
theorem ENERGY_GALERKIN_TIME_TEST_IDENTITY
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    physicalFieldInner (g.velocity t) (φ t) -
      physicalFieldInner (g.velocity s) (φ s) =
    ∫ r in s..t,
      physicalFieldInner (g.velocity r) (timeDerivative φ r) +
      ν * physicalFieldInner (g.velocity r) (laplacian (φ r)) +
      criticalWeakTransport (g.velocity r)
        (finiteSynthesis N (datumFourierCoeff (φ r))) := by
  obtain ⟨hTime, hLap, hTransport⟩ :=
    ENERGY_GALERKIN_TIME_TEST_INTEGRABLE g φ hφ s t hs hst
  have hI := (hTime.add (hLap.const_mul ν)).add hTransport
  have hC : ContinuousOn (fun r => physicalFieldInner (g.velocity r) (φ r)) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (g.velocity r x) (φ r x))
      ((energyGalerkin_velocity_continuousOn g).inner hφ.smooth.continuousOn) s t hs
  have hd : ∀ r ∈ Ioo s t,
      HasDerivAt (fun q => physicalFieldInner (g.velocity q) (φ q))
        (physicalFieldInner (g.velocity r) (timeDerivative φ r) +
          ν * physicalFieldInner (g.velocity r) (laplacian (φ r)) +
          criticalWeakTransport (g.velocity r)
            (finiteSynthesis N (datumFourierCoeff (φ r)))) r := by
    intro r hr
    have h := ENERGY_GALERKIN_PAIRING_HASDERIV g φ hφ r (hs.trans hr.1)
    rw [energyGalerkin_projected_test_pairing g φ hφ r (hs.trans hr.1), ← add_assoc] at h
    exact h
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hC hd hI).symm

end

end QuasiFeffermanB
