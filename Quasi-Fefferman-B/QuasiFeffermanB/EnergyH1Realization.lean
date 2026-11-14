import QuasiFeffermanB.PhysicalFourierL2
import SingularClosure.CriticalSmoothParseval
import SingularClosure.CriticalGradientEnergyBound

/-! Concrete homogeneous-H1 Fourier derivatives and their physical L2
realization. Every operator below acts on the actual coefficient array. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_derivativeSymbol_norm_le_critical (j : Fin 3) (k : Frequency) :
    ‖derivativeSymbol j k‖ ≤ criticalFrequencyWeight k := by
  have hn : ‖derivativeSymbol j k‖ ^ 2 = (2 * Real.pi * (k j : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [derivativeSymbol, Complex.normSq_apply, pow_two]
  have hs : (2 * Real.pi * (k j : ℝ)) ^ 2 ≤ laplacianFrequency k := by
    rw [← sum_derivativeScale_sq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (2 * Real.pi * (k i : ℝ)))
      (Finset.mem_univ j)
  by_cases hk : k = 0
  · subst k
    simp [derivativeSymbol]
  · apply (sq_le_sq₀ (norm_nonneg _) (criticalFrequencyWeight_pos k).le).mp
    rw [hn, criticalFrequencyWeight_sq_of_ne_zero k hk]
    exact hs

theorem energy_derivative_weighted_bound (j : Fin 3) (c : FourierCoeff)
    (ki : FourierIndex) :
    ‖criticalWeightedCoeff 0 (spectralMultiplier (derivativeSymbol j) c) ki‖ ≤
      ‖criticalWeightedCoeff 2 c ki‖ := by
  have hmul : ‖derivativeSymbol j ki.1‖ * ‖c ki.1 ki.2‖ ≤
      criticalFrequencyWeight ki.1 * ‖c ki.1 ki.2‖ :=
    mul_le_mul_of_nonneg_right (energy_derivativeSymbol_norm_le_critical j ki.1)
      (norm_nonneg (c ki.1 ki.2))
  simpa only [criticalWeightedCoeff_norm, zpow_zero, zpow_ofNat, pow_zero,
    one_mul, criticalHalfWeight_sq, spectralMultiplier, norm_mul] using hmul

def energyDerivativeValue (j : Fin 3) (c : CriticalSobolev 2) : CriticalSobolev 0 :=
  criticalSobolevOfCoeff 0 (spectralMultiplier (derivativeSymbol j) (criticalCoeff 2 c))
    ((criticalCoeff_mem 2 c).mono' (energy_derivative_weighted_bound j (criticalCoeff 2 c)))

@[simp] theorem energyDerivativeValue_coeff (j : Fin 3) (c : CriticalSobolev 2) :
    criticalCoeff 0 (energyDerivativeValue j c) =
      spectralMultiplier (derivativeSymbol j) (criticalCoeff 2 c) := by
  apply criticalSobolevOfCoeff_coeff

def energyDerivativeLinear (j : Fin 3) : CriticalSobolev 2 →ₗ[ℂ] CriticalSobolev 0 where
  toFun := energyDerivativeValue j
  map_add' c d := by
    apply criticalCoeff_injective 0
    simp only [energyDerivativeValue_coeff, criticalCoeff_add]
    funext k i
    simp only [spectralMultiplier, Pi.add_apply, mul_add]
  map_smul' z c := by
    apply criticalCoeff_injective 0
    simp only [energyDerivativeValue_coeff, criticalCoeff_smul]
    funext k i
    simp only [spectralMultiplier, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem energyDerivativeLinear_norm_le (j : Fin 3) (c : CriticalSobolev 2) :
    ‖energyDerivativeLinear j c‖ ≤ ‖c‖ := by
  rw [← (criticalSobolevRepr 0).norm_map, ← (criticalSobolevRepr 2).norm_map]
  apply lp.norm_mono (by norm_num)
  intro ki
  simp only [criticalSobolevRepr_apply]
  change ‖criticalWeightedCoeff 0 (criticalCoeff 0 (energyDerivativeValue j c)) ki‖ ≤ _
  rw [energyDerivativeValue_coeff]
  exact energy_derivative_weighted_bound j (criticalCoeff 2 c) ki

def energyDerivative (j : Fin 3) : CriticalSobolev 2 →L[ℂ] CriticalSobolev 0 :=
  (energyDerivativeLinear j).mkContinuous 1
    (fun c => by simpa only [one_mul] using energyDerivativeLinear_norm_le j c)

@[simp] theorem energyDerivative_coeff (j : Fin 3) (c : CriticalSobolev 2) :
    criticalCoeff 0 (energyDerivative j c) =
      spectralMultiplier (derivativeSymbol j) (criticalCoeff 2 c) :=
  energyDerivativeValue_coeff j c

theorem energyDerivative_cutoff (j : Fin 3) (c : CriticalSobolev 2) (N : ℕ) :
    energyDerivative j (criticalFiniteSobolev 2 N (criticalCoeff 2 c)) =
      criticalFiniteSobolev 0 N (criticalCoeff 0 (energyDerivative j c)) := by
  apply criticalCoeff_injective 0
  simp only [energyDerivative_coeff, criticalFiniteSobolev_coeff]
  funext k i
  by_cases hk : k ∈ cutoffModes N <;>
    simp [spectralMultiplier, cutoffCoeff, hk]

def energyPhysicalColumn (j : Fin 3) : CriticalSobolev 2 →L[ℝ] PhysicalCubeL2 :=
  torusToPhysicalCubeL2.comp
    (((torusSobolevL2.toContinuousLinearMap.comp
      criticalH0Equiv.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      ((energyDerivative j).restrictScalars ℝ))

@[simp] theorem energyPhysicalColumn_eq (j : Fin 3) (c : CriticalSobolev 2) :
    energyPhysicalColumn j c = zeroSobolevPhysicalL2 (energyDerivative j c) := rfl

theorem energyPhysicalColumn_fourierCoeff (j : Fin 3) (c : CriticalSobolev 2)
    (hr : SpectralReality (criticalCoeff 2 c)) :
    datumFourierCoeff (energyPhysicalColumn j c : Field) =
      spectralMultiplier (derivativeSymbol j) (criticalCoeff 2 c) := by
  have hz : SpectralMeanZero (criticalCoeff 0 (energyDerivative j c)) := by
    intro i
    simp [energyDerivative_coeff, spectralMultiplier, derivativeSymbol]
  rw [energyPhysicalColumn_eq, zeroSobolevPhysicalL2_fourierCoeff _
    (by simpa only [energyDerivative_coeff] using derivativeMultiplier_reality _ hr j) hz,
    energyDerivative_coeff]

theorem energyPhysicalColumn_finite (j : Fin 3) (c : CriticalSobolev 2)
    (hr : SpectralReality (criticalCoeff 2 c)) (N : ℕ) :
    energyPhysicalColumn j (criticalFiniteSobolev 2 N (criticalCoeff 2 c)) =
      physicalFieldL2 (coordinateDerivative (finiteSynthesis N (criticalCoeff 2 c)) j)
        (coordinateDerivative_continuous (finiteSynthesis_contDiff N _) j) := by
  rw [energyPhysicalColumn_eq, energyDerivative_cutoff]
  rw [zeroSobolevPhysicalL2_finite (energyDerivative j c)
    (by simpa only [energyDerivative_coeff] using derivativeMultiplier_reality _ hr j) N]
  apply Lp.ext
  filter_upwards [physicalFieldL2_coe _ _, physicalFieldL2_coe _ _] with x hx hy
  rw [hx, hy, finiteSynthesis_coordinateDerivative, energyDerivative_coeff]

def energyColumnInsertionLinear (j : Fin 3) : Vec →ₗ[ℝ] (Vec →L[ℝ] Vec) where
  toFun y := (EuclideanSpace.proj j).smulRight y
  map_add' y z := by ext x; simp [smul_add]
  map_smul' r y := by ext x; simp [smul_smul, mul_comm]

def energyColumnInsertion (j : Fin 3) : Vec →L[ℝ] (Vec →L[ℝ] Vec) :=
  (energyColumnInsertionLinear j).toContinuousLinearMap

abbrev EnergyPhysicalGradientL2 := Lp (Vec →L[ℝ] Vec) 2 (volume.restrict unitCube)

def energyPhysicalGradient : CriticalSobolev 2 →L[ℝ] EnergyPhysicalGradientL2 :=
  ∑ j : Fin 3,
    ((energyColumnInsertion j).compLpL 2 (volume.restrict unitCube)).comp
      (energyPhysicalColumn j)

theorem energy_Lp_sum_coe {E ι : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → Lp E 2 (volume.restrict unitCube)) :
    ((∑ i ∈ s, f i : Lp E 2 (volume.restrict unitCube)) : Vec → E)
      =ᵐ[volume.restrict unitCube] (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero E 2 (volume.restrict unitCube)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add Filter.EventuallyEq.rfl ih)

theorem energyPhysicalGradient_coe (c : CriticalSobolev 2) :
    (energyPhysicalGradient c : Vec → (Vec →L[ℝ] Vec)) =ᵐ[volume.restrict unitCube]
      (fun x => ∑ j : Fin 3, (EuclideanSpace.proj j).smulRight (energyPhysicalColumn j c x)) := by
  have hsum := energy_Lp_sum_coe Finset.univ (fun j : Fin 3 =>
    (energyColumnInsertion j).compLpL 2 (volume.restrict unitCube) (energyPhysicalColumn j c))
  have hall : ∀ᵐ x ∂volume.restrict unitCube, ∀ j : Fin 3,
      (energyColumnInsertion j).compLpL 2 (volume.restrict unitCube)
        (energyPhysicalColumn j c) x =
        (EuclideanSpace.proj j).smulRight (energyPhysicalColumn j c x) := by
    rw [ae_all_iff]
    intro j
    exact (energyColumnInsertion j).coeFn_compLpL (energyPhysicalColumn j c)
  have heq : energyPhysicalGradient c = ∑ j : Fin 3,
      (energyColumnInsertion j).compLpL 2 (volume.restrict unitCube)
        (energyPhysicalColumn j c) := by
    simp only [energyPhysicalGradient, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply]
  rw [heq]
  filter_upwards [hsum, hall] with x hx hy
  rw [hx]
  simp_rw [hy]

theorem energyPhysicalGradient_finite (c : CriticalSobolev 2)
    (hr : SpectralReality (criticalCoeff 2 c)) (N : ℕ) :
    (energyPhysicalGradient (criticalFiniteSobolev 2 N (criticalCoeff 2 c)) :
      Vec → (Vec →L[ℝ] Vec)) =ᵐ[volume.restrict unitCube]
        fderiv ℝ (finiteSynthesis N (criticalCoeff 2 c)) := by
  have hall : ∀ᵐ x ∂volume.restrict unitCube, ∀ j : Fin 3,
      energyPhysicalColumn j (criticalFiniteSobolev 2 N (criticalCoeff 2 c)) x =
        coordinateDerivative (finiteSynthesis N (criticalCoeff 2 c)) j x := by
    rw [ae_all_iff]
    intro j
    rw [energyPhysicalColumn_finite j c hr N]
    exact physicalFieldL2_coe _ _
  filter_upwards [energyPhysicalGradient_coe (criticalFiniteSobolev 2 N (criticalCoeff 2 c)),
    hall] with x hx hy
  rw [hx]
  simp_rw [hy]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  change (∑ j : Fin 3, y j •
    fderiv ℝ (finiteSynthesis N (criticalCoeff 2 c)) x (unitVector j)) = _
  exact (critical_matrix_apply_eq_sum (fderiv ℝ (finiteSynthesis N (criticalCoeff 2 c)) x) y).symm

/-- Every real, mean-zero homogeneous-H1 Fourier field has the literal
physical H1 closure required by the Leray--Hopf definition. -/
theorem ENERGY_FOURIER_H1_PHYSICAL_REALIZATION (c : CriticalSobolev 2)
    (hr : SpectralReality (criticalCoeff 2 c))
    (hz : SpectralMeanZero (criticalCoeff 2 c)) :
    CriticalPhysicalH1
      (zeroSobolevPhysicalL2 (criticalSobolevLower 0 2 (by norm_num) c) : Field)
      (energyPhysicalGradient c : Vec → (Vec →L[ℝ] Vec)) := by
  let v : PhysicalCubeL2 :=
    zeroSobolevPhysicalL2 (criticalSobolevLower 0 2 (by norm_num) c)
  have hvcoeff : datumFourierCoeff (v : Field) = criticalCoeff 2 c := by
    dsimp only [v]
    rw [zeroSobolevPhysicalL2_fourierCoeff _
      (by simpa only [criticalSobolevLower_coeff] using hr)
      (by simpa only [criticalSobolevLower_coeff] using hz), criticalSobolevLower_coeff]
  have hvel := physicalL2_cutoff_eLpNorm_tendsto (v : Field) (Lp.memLp v)
    (by simpa only [hvcoeff] using hz)
  have hgrad := (energyPhysicalGradient.continuous.continuousAt.tendsto.comp
    (criticalFiniteSobolev_tendsto 2 c hz)).sub_const (energyPhysicalGradient c)
  have hgradnorm := hgrad.enorm
  have heq (N : ℕ) :
      ‖energyPhysicalGradient (criticalFiniteSobolev 2 N (criticalCoeff 2 c)) -
        energyPhysicalGradient c‖ₑ =
      eLpNorm (fderiv ℝ (finiteSynthesis N (criticalCoeff 2 c)) -
        (energyPhysicalGradient c : Vec → (Vec →L[ℝ] Vec))) 2
        (volume.restrict unitCube) := by
    rw [Lp.enorm_def]
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans
      ((energyPhysicalGradient_finite c hr N).sub Filter.EventuallyEq.rfl)
  refine ⟨Lp.memLp v, Lp.memLp (energyPhysicalGradient c),
    ⟨fun N => finiteSynthesis N (criticalCoeff 2 c),
      (fun N => finiteSynthesis_contDiff N _),
      (fun N => finiteSynthesis_periodic N _), ?_, ?_⟩⟩
  · simpa only [hvcoeff] using hvel
  · simpa only [Function.comp_def, heq, sub_self, enorm_zero] using hgradnorm

theorem energyPhysicalGradient_column (c : CriticalSobolev 2) (j : Fin 3) :
    (fun x => energyPhysicalGradient c x (unitVector j))
      =ᵐ[volume.restrict unitCube] (energyPhysicalColumn j c : Field) := by
  filter_upwards [energyPhysicalGradient_coe c] with x hx
  rw [hx]
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    unitVector, energyColumnInsertion, energyColumnInsertionLinear]

theorem energyDerivative_sum_norm_sq (c : CriticalSobolev 2)
    (hz : SpectralMeanZero (criticalCoeff 2 c)) :
    (∑ j : Fin 3, ‖energyDerivative j c‖ ^ 2) = ‖c‖ ^ 2 := by
  have hs := critical_H1_laplacian_summable c hz
  have hd (j : Fin 3) : Summable (fun ki : FourierIndex =>
      Complex.normSq (spectralMultiplier (derivativeSymbol j) (criticalCoeff 2 c)
        ki.1 ki.2)) := by
    apply Summable.of_nonneg_of_le (fun _ => Complex.normSq_nonneg _) _ hs
    intro ki
    rw [← critical_sum_derivative_normSq (criticalCoeff 2 c) ki.1 ki.2]
    exact Finset.single_le_sum (fun l _ => Complex.normSq_nonneg
      (spectralMultiplier (derivativeSymbol l) (criticalCoeff 2 c) ki.1 ki.2))
      (Finset.mem_univ j)
  simp_rw [criticalSobolev_norm_sq 0, zpow_zero, one_mul, energyDerivative_coeff]
  rw [← Summable.tsum_finsetSum (fun j _ => hd j), criticalSobolev_norm_sq 2]
  apply tsum_congr
  intro ki
  rw [critical_sum_derivative_normSq,
    critical_weight_two_laplacian (criticalCoeff 2 c) hz]

/-- The physical coordinate-gradient energy equals the exact homogeneous-H1
Fourier energy; no operator-norm equivalence constant enters this identity. -/
theorem energyPhysicalGradient_energy (c : CriticalSobolev 2)
    (hr : SpectralReality (criticalCoeff 2 c))
    (hz : SpectralMeanZero (criticalCoeff 2 c)) :
    criticalGradientEnergy (energyPhysicalGradient c : Vec → (Vec →L[ℝ] Vec)) =
      ‖c‖ ^ 2 := by
  have he (j : Fin 3) :
      physicalEnergy (fun x => energyPhysicalGradient c x (unitVector j)) =
        ‖energyDerivative j c‖ ^ 2 := by
    have hcol : physicalEnergy (fun x => energyPhysicalGradient c x (unitVector j)) =
        physicalEnergy (energyPhysicalColumn j c : Field) := by
      simp only [physicalEnergy_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [energyPhysicalGradient_column c j] with x hx
      rw [hx]
    rw [hcol, physicalEnergy_eq_toLp_norm_sq _ (Lp.memLp _), Lp.toLp_coeFn,
      energyPhysicalColumn_eq]
    congr 1
    apply zeroSobolevPhysicalL2_norm
    · simpa only [energyDerivative_coeff] using derivativeMultiplier_reality _ hr j
    · intro i
      simp [energyDerivative_coeff, spectralMultiplier, derivativeSymbol]
  simp only [criticalGradientEnergy, he]
  exact energyDerivative_sum_norm_sq c hz

end
end QuasiFeffermanB
