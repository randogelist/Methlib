import SingularClosure.CriticalCubeL2
import SingularClosure.CriticalGalerkin

/-! Exact physical Fourier recovery for arbitrary real mean-zero Hhalf data.

The physical Fourier integral is first identified with a continuous linear
functional on real cube L2. Finite Fourier synthesis has the exact cutoff
coefficients, and density in the actual weighted Hilbert norm passes that
identity to every rough datum. No solution, smallness, or evolution is used.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace SingularClosure

noncomputable section

def criticalCubeCharacterL2 (k : Frequency) : Lp ℂ 2 (volume.restrict unitCube) :=
  (critical_continuous_memLp_cube (fourierCharacter k)
    (fourierCharacter_contDiff k).continuous 2).toLp (fourierCharacter k)

def criticalCubeComplexCoordinate (i : Fin 3) : Vec →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)

/-- The literal physical Fourier integral is a bounded functional on real cube L2. -/
def criticalCubeFourierFunctional (k : Frequency) (i : Fin 3) :
    PhysicalCubeL2 →L[ℝ] ℂ :=
  ((innerSL ℂ (criticalCubeCharacterL2 k)).restrictScalars ℝ).comp
    ((criticalCubeComplexCoordinate i).compLpL 2 (volume.restrict unitCube))

theorem criticalCubeFourierFunctional_apply
    (k : Frequency) (i : Fin 3) (v : PhysicalCubeL2) :
    criticalCubeFourierFunctional k i v = datumFourierCoeff (v : Field) k i := by
  change inner ℂ (criticalCubeCharacterL2 k)
    ((criticalCubeComplexCoordinate i).compLpL 2 (volume.restrict unitCube) v) = _
  rw [L2.inner_def]
  unfold datumFourierCoeff datumFourierIntegrand
  apply integral_congr_ae
  have hchar := (critical_continuous_memLp_cube (fourierCharacter k)
    (fourierCharacter_contDiff k).continuous 2).coeFn_toLp
  have hcoord := (criticalCubeComplexCoordinate i).coeFn_compLpL v
  filter_upwards [hchar, hcoord] with x hx hxi
  change inner ℂ (criticalCubeCharacterL2 k x)
      (((criticalCubeComplexCoordinate i).compLpL 2 (volume.restrict unitCube) v) x) = _
  change criticalCubeCharacterL2 k x = fourierCharacter k x at hx
  rw [hx, hxi]
  simp only [criticalCubeComplexCoordinate, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj, Complex.ofRealCLM_apply, RCLike.inner_apply,
    Complex.star_def, mul_comm]

theorem criticalCube_datumFourierCoeff_congr_ae
    {v w : Field} (h : v =ᵐ[volume.restrict unitCube] w) :
    datumFourierCoeff v = datumFourierCoeff w := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem criticalCubeFourierFunctional_physicalField
    (k : Frequency) (i : Fin 3) (v : Field) (hv : Continuous v) :
    criticalCubeFourierFunctional k i (physicalFieldL2 v hv) = datumFourierCoeff v k i := by
  rw [criticalCubeFourierFunctional_apply,
    criticalCube_datumFourierCoeff_congr_ae (physicalFieldL2_coe v hv)]

theorem criticalInitialPhysicalL2_continuous :
    Continuous criticalInitialPhysicalL2 :=
  torusToPhysicalCubeL2.continuous.comp (criticalPhysicalL2 1 (by norm_num)).continuous

/-- Actual finite rough cutoffs realize the same real physical Fourier polynomial. -/
theorem criticalInitialPhysicalL2_finite
    (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a)) (N : ℕ) :
    criticalInitialPhysicalL2 (criticalFiniteSobolev 1 N (criticalCoeff 1 a)) =
      physicalFieldL2 (finiteSynthesis N (criticalCoeff 1 a))
        (finiteSynthesis_contDiff N (criticalCoeff 1 a)).continuous := by
  have heq : criticalPhysicalL2 1 (by norm_num)
      (criticalFiniteSobolev 1 N (criticalCoeff 1 a)) =
      torusPhysicalFieldL2 (finiteSynthesis N (criticalCoeff 1 a))
        (finiteSynthesis_contDiff N (criticalCoeff 1 a)).continuous := by
    apply torusVectorFourierCoeff_injective
    rw [criticalPhysicalL2_fourierCoeff, criticalFiniteSobolev_coeff,
      torusPhysicalFieldL2_fourierCoeff,
      criticalGalerkin_datumFourierCoeff_finiteSynthesis N (criticalCoeff 1 a) hreal]
  change torusToPhysicalCubeL2
    (criticalPhysicalL2 1 (by norm_num) (criticalFiniteSobolev 1 N (criticalCoeff 1 a))) = _
  rw [heq]
  exact torusToPhysicalCubeL2_physicalField _ _ (finiteSynthesis_periodic N (criticalCoeff 1 a))

/-- The canonical real cube representative has exactly the original rough
Fourier coefficients, independently of all NSE construction and smallness. -/
theorem criticalInitialPhysicalL2_fourierCoeff
    (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    datumFourierCoeff (criticalInitialPhysicalL2 a : Field) = criticalCoeff 1 a := by
  have hcut := criticalFiniteSobolev_tendsto 1 a hzero
  have hphysical := criticalInitialPhysicalL2_continuous.continuousAt.tendsto.comp hcut
  funext k i
  have hleft := (criticalCubeFourierFunctional k i).continuous.continuousAt.tendsto.comp hphysical
  have hright := (criticalCoeff_continuous 1 k i).continuousAt.tendsto.comp hcut
  have heq (N : ℕ) : criticalCubeFourierFunctional k i
      (criticalInitialPhysicalL2 (criticalFiniteSobolev 1 N (criticalCoeff 1 a))) =
      criticalCoeff 1 (criticalFiniteSobolev 1 N (criticalCoeff 1 a)) k i := by
    rw [criticalInitialPhysicalL2_finite a hreal N,
      criticalCubeFourierFunctional_physicalField,
      criticalGalerkin_datumFourierCoeff_finiteSynthesis N (criticalCoeff 1 a) hreal,
      criticalFiniteSobolev_coeff]
  have hleft' : Tendsto
      (fun N => criticalCoeff 1 (criticalFiniteSobolev 1 N (criticalCoeff 1 a)) k i)
      atTop (𝓝 (datumFourierCoeff (criticalInitialPhysicalL2 a : Field) k i)) := by
    simpa only [Function.comp_def, heq, criticalCubeFourierFunctional_apply] using hleft
  exact tendsto_nhds_unique hleft' hright

/-- Reality is retained by the real cube map without losing any admissible datum. -/
theorem criticalInitialPhysicalL2_injective_on_real_meanZero
    (a b : CriticalSobolev 1)
    (ha : SpectralReality (criticalCoeff 1 a)) (hb : SpectralReality (criticalCoeff 1 b))
    (hza : SpectralMeanZero (criticalCoeff 1 a)) (hzb : SpectralMeanZero (criticalCoeff 1 b))
    (h : criticalInitialPhysicalL2 a = criticalInitialPhysicalL2 b) : a = b := by
  apply criticalCoeff_injective 1
  rw [← criticalInitialPhysicalL2_fourierCoeff a ha hza,
    ← criticalInitialPhysicalL2_fourierCoeff b hb hzb, h]

/-- On real mean-zero data the cube map preserves the unweighted Fourier L2 norm. -/
theorem criticalInitialPhysicalL2_norm
    (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    ‖criticalInitialPhysicalL2 a‖ = ‖criticalSobolevLower 0 1 (by norm_num) a‖ := by
  have hfinite (N : ℕ) :
      ‖criticalInitialPhysicalL2 (criticalFiniteSobolev 1 N (criticalCoeff 1 a))‖ ^ 2 =
      ‖criticalSobolevLower 0 1 (by norm_num)
        (criticalFiniteSobolev 1 N (criticalCoeff 1 a))‖ ^ 2 := by
    have hlower : criticalSobolevLower 0 1 (by norm_num)
        (criticalFiniteSobolev 1 N (criticalCoeff 1 a)) =
        criticalFiniteSobolev 0 N (criticalCoeff 1 a) := by
      apply criticalCoeff_injective 0
      rw [criticalSobolevLower_coeff, criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff]
    rw [criticalInitialPhysicalL2_finite a hreal N, physicalFieldL2_norm_sq,
      FINITE_PHYSICAL_ENERGY_PARSEVAL N (criticalCoeff 1 a) hreal,
      hlower, criticalFiniteSobolev_norm_sq]
    simp only [coefficientEnergy, zpow_zero, one_mul]
  have hcut := criticalFiniteSobolev_tendsto 1 a hzero
  have hleft := (criticalInitialPhysicalL2_continuous.continuousAt.tendsto.comp hcut).norm.pow 2
  have hright := ((criticalSobolevLower 0 1 (by norm_num)).continuous.continuousAt.tendsto.comp
    hcut).norm.pow 2
  have hleft' : Tendsto
      (fun N => ‖criticalSobolevLower 0 1 (by norm_num)
        (criticalFiniteSobolev 1 N (criticalCoeff 1 a))‖ ^ 2)
      atTop (𝓝 (‖criticalInitialPhysicalL2 a‖ ^ 2)) := by
    simpa only [Function.comp_def, hfinite] using hleft
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (tendsto_nhds_unique hleft' hright)

theorem criticalInitialPhysicalL2_norm_sq
    (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    ‖criticalInitialPhysicalL2 a‖ ^ 2 =
      ∑' ki : FourierIndex, Complex.normSq (criticalCoeff 1 a ki.1 ki.2) := by
  rw [criticalInitialPhysicalL2_norm a hreal hzero, criticalSobolev_norm_sq]
  simp only [criticalSobolevLower_coeff, zpow_zero, one_mul]

end

end SingularClosure
