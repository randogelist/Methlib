import QuasiFeffermanB.FourierEnergy
import QuasiFeffermanB.MeanPreservation
import SingularClosure.CriticalRegularityContracts

/-! Distributional physical solenoidality implies the literal Fourier
constraints. The complex character test is derived from two permitted real
scalar tests. No spectral admissibility assumption replaces the physical one. -/

set_option autoImplicit false
set_option Elab.async true
noncomputable section
open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology

namespace QuasiFeffermanB

theorem physical_constant_pairing_coordinate (v : Field) (i : Fin 3) :
    physicalFieldInner v (fun _ => unitVector i) = ∫ x in unitCube, v x i := by
  unfold physicalFieldInner
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [unitVector, PiLp.inner_apply, RCLike.inner_apply]

theorem physical_mean_pairings_fourier_zero (v : Field)
    (hmean : ∀ i : Fin 3, physicalFieldInner v (fun _ => unitVector i) = 0) :
    SpectralMeanZero (datumFourierCoeff v) := by
  intro i
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [fourierCharacter, Pi.zero_apply, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    star_one, one_mul]
  rw [integral_complex_ofReal, ← physical_constant_pairing_coordinate v i, hmean i]
  rfl

theorem physical_complex_coordinate_memLp (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (i : Fin 3) :
    MemLp (fun x => (v x i : ℂ)) 2 (volume.restrict unitCube) := by
  simpa only [criticalCubeComplexCoordinate, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, EuclideanSpace.coe_proj, Function.comp_def] using
    (criticalCubeComplexCoordinate i).comp_memLp' hv

theorem physical_datumFourierIntegrand_integrable (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (k : Frequency) (i : Fin 3) :
    IntegrableOn (datumFourierIntegrand v k i) unitCube volume := by
  have hc := critical_continuous_memLp_cube (fourierCharacter (-k))
    (fourierCharacter_contDiff (-k)).continuous 2
  have h := hc.integrable_mul (q := 2) (physical_complex_coordinate_memLp v hv i)
  change Integrable
    (fun x => fourierCharacter (-k) x * (v x i : ℂ)) (volume.restrict unitCube) at h
  change Integrable
    (fun x => star (fourierCharacter k x) * (v x i : ℂ)) (volume.restrict unitCube)
  simpa only [fourierCharacter_neg] using h

theorem complex_derivative_real_component (f : Vec → ℂ)
    (hf : Differentiable ℝ f) (x : Vec) (i : Fin 3) :
    fderiv ℝ (fun y => (f y).re) x (unitVector i) =
      (fderiv ℝ f x (unitVector i)).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) h.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, Complex.reCLM_apply] using he

theorem complex_derivative_imaginary_component (f : Vec → ℂ)
    (hf : Differentiable ℝ f) (x : Vec) (i : Fin 3) :
    fderiv ℝ (fun y => (f y).im) x (unitVector i) =
      (fderiv ℝ f x (unitVector i)).im := by
  have h := Complex.imCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  have he := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) h.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, Complex.imCLM_apply] using he

/-- Two real scalar tests give the actual complex gradient test identity. -/
theorem physical_complex_gradient_annihilation (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hgrad : ∀ p : Vec → ℝ, ContDiff ℝ ∞ p → SpatialPeriodic p →
      physicalFieldInner v (SingularClosure.gradient p) = 0)
    (f : Vec → ℂ) (hf : ContDiff ℝ ∞ f) (hfp : SpatialPeriodic f) :
    (∫ x in unitCube, ∑ i : Fin 3,
      (v x i : ℂ) * fderiv ℝ f x (unitVector i)) = 0 := by
  have hD (i : Fin 3) : Continuous (fun x => fderiv ℝ f x (unitVector i)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hterm (i : Fin 3) : IntegrableOn
      (fun x => (v x i : ℂ) * fderiv ℝ f x (unitVector i)) unitCube volume := by
    exact (physical_complex_coordinate_memLp v hv i).integrable_mul (q := 2)
      (critical_continuous_memLp_cube _ (hD i) 2)
  have hint : IntegrableOn
      (fun x => ∑ i : Fin 3, (v x i : ℂ) * fderiv ℝ f x (unitVector i)) unitCube volume :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  have hR (x : Vec) :
      (∑ i : Fin 3, (v x i : ℂ) * fderiv ℝ f x (unitVector i)).re =
        inner ℝ (v x) (SingularClosure.gradient (fun y => (f y).re) x) := by
    simp [SingularClosure.gradient, PiLp.inner_apply, RCLike.inner_apply,
      complex_derivative_real_component f (hf.differentiable (by simp)), mul_comm]
  have hI (x : Vec) :
      (∑ i : Fin 3, (v x i : ℂ) * fderiv ℝ f x (unitVector i)).im =
        inner ℝ (v x) (SingularClosure.gradient (fun y => (f y).im) x) := by
    simp [SingularClosure.gradient, PiLp.inner_apply, RCLike.inner_apply,
      complex_derivative_imaginary_component f (hf.differentiable (by simp)), mul_comm]
  have hpR : SpatialPeriodic (fun x => (f x).re) := by
    intro x i
    exact congrArg Complex.re (hfp x i)
  have hpI : SpatialPeriodic (fun x => (f x).im) := by
    intro x i
    exact congrArg Complex.im (hfp x i)
  apply Complex.ext
  · calc
      (∫ x in unitCube, ∑ i : Fin 3,
          (v x i : ℂ) * fderiv ℝ f x (unitVector i)).re =
          ∫ x in unitCube, (∑ i : Fin 3,
            (v x i : ℂ) * fderiv ℝ f x (unitVector i)).re :=
        (Complex.reCLM.integral_comp_comm hint).symm
      _ = physicalFieldInner v (SingularClosure.gradient (fun x => (f x).re)) := by
        simp only [hR, physicalFieldInner]
      _ = 0 := hgrad _ (Complex.reCLM.contDiff.comp hf) hpR
  · calc
      (∫ x in unitCube, ∑ i : Fin 3,
          (v x i : ℂ) * fderiv ℝ f x (unitVector i)).im =
          ∫ x in unitCube, (∑ i : Fin 3,
            (v x i : ℂ) * fderiv ℝ f x (unitVector i)).im :=
        (Complex.imCLM.integral_comp_comm hint).symm
      _ = physicalFieldInner v (SingularClosure.gradient (fun x => (f x).im)) := by
        simp only [hI, physicalFieldInner]
      _ = 0 := hgrad _ (Complex.imCLM.contDiff.comp hf) hpI

theorem physical_gradient_annihilation_fourier_solenoidal (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hgrad : ∀ p : Vec → ℝ, ContDiff ℝ ∞ p → SpatialPeriodic p →
      physicalFieldInner v (SingularClosure.gradient p) = 0) :
    SpectralSolenoidal (datumFourierCoeff v) := by
  intro k
  have hz := physical_complex_gradient_annihilation v hv hgrad
    (fourierCharacter (-k)) (fourierCharacter_contDiff (-k)) (fourierCharacter_periodic (-k))
  have hpoint (x : Vec) :
      (∑ i : Fin 3, (v x i : ℂ) * fderiv ℝ (fourierCharacter (-k)) x (unitVector i)) =
        -(∑ i : Fin 3, derivativeSymbol i k * datumFourierIntegrand v k i x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(fourierCharacter_hasFDerivAt (-k) x).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fourierPhaseCLM_unitVector,
      fourierCharacter_neg, datumFourierIntegrand, derivativeSymbol, Pi.neg_apply,
      Int.cast_neg, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast]
    ring
  simp_rw [hpoint] at hz
  rw [integral_neg] at hz
  have hcoeff : (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff v k i) = 0 := by
    have h := neg_eq_zero.mp hz
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (physical_datumFourierIntegrand_integrable v hv k i).const_mul (derivativeSymbol i k))] at h
    simpa only [integral_const_mul, datumFourierCoeff] using h
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hfactor :
      (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff v k i) =
        C * ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff v k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, C]
    ring
  have hC : C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hfactor] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hC

theorem EnergySigmaZero.fourier_constraints {a : CriticalPhysicalL2}
    (ha : EnergySigmaZero a) :
    SpectralReality (datumFourierCoeff (a : Field)) ∧
    SpectralSolenoidal (datumFourierCoeff (a : Field)) ∧
    SpectralMeanZero (datumFourierCoeff (a : Field)) := by
  exact ⟨datumFourierCoeff_reality _,
    physical_gradient_annihilation_fourier_solenoidal _ (Lp.memLp a) ha.gradient_annihilation,
    physical_mean_pairings_fourier_zero _ ha.mean_zero⟩

theorem physicalH1HalfDatum_criticalSigmaZero
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G)
    (hgrad : ∀ p : Vec → ℝ, ContDiff ℝ ∞ p → SpatialPeriodic p →
      physicalFieldInner v (SingularClosure.gradient p) = 0)
    (hmean : ∀ i : Fin 3, physicalFieldInner v (fun _ => unitVector i) = 0) :
    CriticalSigmaZero
      (physicalH1HalfDatum hv (physical_mean_pairings_fourier_zero v hmean)) := by
  constructor
  · rw [physicalH1HalfDatum_coeff]
    exact datumFourierCoeff_reality v
  · rw [physicalH1HalfDatum_coeff]
    exact physical_gradient_annihilation_fourier_solenoidal v hv.velocity_L2 hgrad
  · rw [physicalH1HalfDatum_coeff]
    exact physical_mean_pairings_fourier_zero v hmean

theorem LH_POSITIVE_TRACE_FOURIER_CONSTRAINTS
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) (ha : EnergySigmaZero a)
    (t : ℝ) (ht : 0 < t) :
    SpectralReality (datumFourierCoeff (u t)) ∧
    SpectralSolenoidal (datumFourierCoeff (u t)) ∧
    SpectralMeanZero (datumFourierCoeff (u t)) := by
  refine ⟨datumFourierCoeff_reality _,
    physical_gradient_annihilation_fourier_solenoidal _ (hu.velocity_L2 t ht.le)
      (hu.momentum.gradient_annihilation t ht), ?_⟩
  apply physical_mean_pairings_fourier_zero
  intro i
  rw [LH_CONSTANT_PAIRING_PRESERVED hu (unitVector i) t ht.le]
  exact ha.mean_zero i

end QuasiFeffermanB
