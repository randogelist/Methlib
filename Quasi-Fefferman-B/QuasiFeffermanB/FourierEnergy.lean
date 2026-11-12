import SingularClosure.CriticalPhysicalH1
import SingularClosure.CriticalGradientEnergyBound
import SingularClosure.CriticalInitialPhysicalFourier
import SingularClosure.CriticalFourierInterpolation
import SingularClosure.InitialCutoffBounds
import SingularClosure.CriticalLerayHopf
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Physical midpoint interpolation. The Fourier coefficients below are the
literal cube integrals. The half-order energy is an extended nonnegative sum;
its finiteness is proved from physical H1 approximation. -/

noncomputable section
open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology

namespace QuasiFeffermanB

theorem physicalEnergy_eq_toLp_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    physicalEnergy v = ‖hv.toLp v‖ ^ 2 := by
  rw [Lp.norm_toLp]
  exact (critical_velocity_L2_toReal_sq_eq_physicalEnergy v hv).symm

theorem physicalEnergy_tendsto_of_L2
    (f : ℕ → Field) (v : Field)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - v) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => physicalEnergy (f n)) atTop (𝓝 (physicalEnergy v)) := by
  have h := (critical_toLp_tendsto_of_eLpNorm_sub f v hf hv hconv).norm.pow 2
  simpa only [← physicalEnergy_eq_toLp_norm_sq] using h

theorem physicalEnergy_compCLM_tendsto_of_L2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Vec) (f : ℕ → Vec → E) (g : Vec → E)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) :
    Tendsto (fun n => physicalEnergy (L ∘ f n)) atTop (𝓝 (physicalEnergy (L ∘ g))) := by
  have hLp := critical_toLp_tendsto_of_eLpNorm_sub f g hf hg hconv
  have hL := ((L.compLpL 2 (volume.restrict unitCube)).continuous.tendsto
    (hg.toLp g)).comp hLp
  have heq (w : Vec → E) (hw : MemLp w 2 (volume.restrict unitCube)) :
      physicalEnergy (L ∘ w) =
        ‖L.compLpL 2 (volume.restrict unitCube) (hw.toLp w)‖ ^ 2 := by
    rw [physicalEnergy_eq_toLp_norm_sq _ (L.comp_memLp' hw),
      critical_toLp_compCLM]
  simpa only [← heq] using hL.norm.pow 2

theorem datumFourierCoeff_tendsto_of_L2
    (f : ℕ → Field) (v : Field)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict unitCube))
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hconv : Tendsto (fun n => eLpNorm (f n - v) 2 (volume.restrict unitCube))
      atTop (𝓝 0)) (k : Frequency) (i : Fin 3) :
    Tendsto (fun n => datumFourierCoeff (f n) k i) atTop
      (𝓝 (datumFourierCoeff v k i)) := by
  have hLp := critical_toLp_tendsto_of_eLpNorm_sub f v hf hv hconv
  have h := ((criticalCubeFourierFunctional k i).continuous.tendsto (hv.toLp v)).comp hLp
  have heq (w : Field) (hw : MemLp w 2 (volume.restrict unitCube)) :
      criticalCubeFourierFunctional k i (hw.toLp w) = datumFourierCoeff w k i := by
    rw [criticalCubeFourierFunctional_apply,
      criticalCube_datumFourierCoeff_congr_ae hw.coeFn_toLp]
  simpa only [heq] using h

theorem physicalH1_cutoff_bounds {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (N : ℕ) :
    coefficientEnergy N (datumFourierCoeff v) ≤ physicalEnergy v ∧
    coefficientDissipation N (datumFourierCoeff v) ≤ criticalGradientEnergy G := by
  obtain ⟨w, hw, hwp, hvelocity, hderivative⟩ := hv.approximation
  have hw2 (n : ℕ) : MemLp (w n) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (hw n).continuous 2
  have hD2 (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ ((hw n).continuous_fderiv (by simp)) 2
  have hcoeff (k : Frequency) (i : Fin 3) :=
    datumFourierCoeff_tendsto_of_L2 w v hw2 hv.velocity_L2 hvelocity k i
  have hnorm (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => Complex.normSq (datumFourierCoeff (w n) k i)) atTop
        (𝓝 (Complex.normSq (datumFourierCoeff v k i))) := by
    simpa only [Complex.normSq_eq_norm_sq] using (hcoeff k i).norm.pow 2
  have hE : Tendsto (fun n => coefficientEnergy N (datumFourierCoeff (w n))) atTop
      (𝓝 (coefficientEnergy N (datumFourierCoeff v))) := by
    unfold coefficientEnergy
    exact tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun i _ => hnorm k i
  have hD : Tendsto (fun n => coefficientDissipation N (datumFourierCoeff (w n))) atTop
      (𝓝 (coefficientDissipation N (datumFourierCoeff v))) := by
    unfold coefficientDissipation
    exact tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun i _ =>
      (hnorm k i).const_mul _
  have hV := physicalEnergy_tendsto_of_L2 w v hw2 hv.velocity_L2 hvelocity
  have hG : Tendsto (fun n => criticalGradientEnergy (fderiv ℝ (w n))) atTop
      (𝓝 (criticalGradientEnergy G)) := by
    unfold criticalGradientEnergy
    apply tendsto_finset_sum
    intro j _
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      physicalEnergy_compCLM_tendsto_of_L2
        (ContinuousLinearMap.apply ℝ Vec (unitVector j))
        (fun n => fderiv ℝ (w n)) G hD2 hv.derivative_L2 hderivative
  constructor
  · exact le_of_tendsto_of_tendsto hE hV (Filter.Eventually.of_forall fun n =>
      coefficientEnergy_initial_cutoff_le N (w n) (hw n).continuous)
  · apply le_of_tendsto_of_tendsto hD hG
    apply Filter.Eventually.of_forall
    intro n
    simpa only [integral_gradientSquareDensity_eq_sum_physicalEnergy _ (hw n),
      criticalGradientEnergy, coordinateDerivative] using
      coefficientDissipation_initial_cutoff_le N (w n) (hw n) (hwp n)

theorem criticalEnergy_midpoint (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 1 N c ^ 2 ≤ coefficientEnergy N c * coefficientDissipation N c := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (cutoffModes N)
    (r := fun k => criticalFrequencyWeight k * ∑ i : Fin 3, Complex.normSq (c k i))
    (f := fun k => ∑ i : Fin 3, Complex.normSq (c k i))
    (g := fun k => criticalFrequencyWeight k ^ 2 * ∑ i : Fin 3, Complex.normSq (c k i))
    (fun k _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (c k i))
    (fun k _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
      Complex.normSq_nonneg (c k i))) (fun k _ => le_of_eq (by ring))
  rw [← criticalEnergy_two_eq_coefficientDissipation]
  simpa only [criticalEnergy, coefficientEnergy, pow_one, Finset.mul_sum] using h

theorem physicalH1_cutoff_midpoint {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (N : ℕ) :
    criticalEnergy 1 N (datumFourierCoeff v) ^ 2 ≤
      physicalEnergy v * criticalGradientEnergy G := by
  obtain ⟨hE, hD⟩ := physicalH1_cutoff_bounds hv N
  apply (criticalEnergy_midpoint N _).trans
  apply mul_le_mul hE hD (coefficientDissipation_nonneg N _)
  rw [physicalEnergy_eq_integral_norm_sq]
  exact integral_nonneg fun x => sq_nonneg _

def physicalHalfEnergyTerm (v : Field) (ki : FourierIndex) : ℝ :=
  if ki.1 = 0 then 0 else
    criticalFrequencyWeight ki.1 * Complex.normSq (datumFourierCoeff v ki.1 ki.2)

theorem physicalHalfEnergyTerm_nonneg (v : Field) (ki : FourierIndex) :
    0 ≤ physicalHalfEnergyTerm v ki := by
  unfold physicalHalfEnergyTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (criticalFrequencyWeight_pos _).le (Complex.normSq_nonneg _)

/-- Infinite critical energy remains `∞` for inadmissible physical data. -/
def physicalHalfEnergy (v : Field) : ℝ≥0∞ :=
  ∑' ki : FourierIndex, ENNReal.ofReal (physicalHalfEnergyTerm v ki)

theorem physicalHalfEnergy_cutoff (v : Field) (N : ℕ) :
    (∑ ki ∈ sobolevCutoffIndices N, ENNReal.ofReal (physicalHalfEnergyTerm v ki)) =
      ENNReal.ofReal (criticalEnergy 1 N (datumFourierCoeff v)) := by
  classical
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ki _ => physicalHalfEnergyTerm_nonneg v ki)]
  congr 1
  rw [sobolevCutoffIndices, Finset.sum_product, sobolevCutoffModes,
    Finset.sum_insert (by
      intro h
      exact ((mem_cutoffModes_iff N 0).mp h).2.1 rfl)]
  simp only [physicalHalfEnergyTerm, if_pos rfl, Finset.sum_const_zero, zero_add]
  unfold criticalEnergy
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  simp only [if_neg hk0, pow_one]

theorem physicalH1_halfEnergy_le {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) :
    physicalHalfEnergy v ≤
      ENNReal.ofReal (Real.sqrt (physicalEnergy v * criticalGradientEnergy G)) := by
  have hlim : Tendsto
      (fun N => ∑ ki ∈ sobolevCutoffIndices N,
        ENNReal.ofReal (physicalHalfEnergyTerm v ki)) atTop (𝓝 (physicalHalfEnergy v)) :=
    ENNReal.summable.hasSum.comp sobolevCutoffIndices_tendsto_atTop
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro N
  rw [physicalHalfEnergy_cutoff]
  apply ENNReal.ofReal_le_ofReal
  have hprod : 0 ≤ physicalEnergy v * criticalGradientEnergy G :=
    mul_nonneg (by
      rw [physicalEnergy_eq_integral_norm_sq]
      exact integral_nonneg fun x => sq_nonneg _) (criticalGradientEnergy_nonneg G)
  exact (Real.le_sqrt (criticalEnergy_nonneg 1 N _) hprod).2
    (physicalH1_cutoff_midpoint hv N)

theorem physicalH1_halfEnergy_ne_top {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) : physicalHalfEnergy v ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (physicalH1_halfEnergy_le hv)

/-- The real readout is used only after finiteness has been proved. -/
theorem physicalH1_halfEnergy_midpoint {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) :
    (physicalHalfEnergy v).toReal ^ 2 ≤ physicalEnergy v * criticalGradientEnergy G := by
  have hnonneg : 0 ≤ physicalEnergy v * criticalGradientEnergy G := by
    apply mul_nonneg _ (criticalGradientEnergy_nonneg G)
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg fun x => sq_nonneg _
  have hle : (physicalHalfEnergy v).toReal ≤
      Real.sqrt (physicalEnergy v * criticalGradientEnergy G) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (physicalH1_halfEnergy_le hv)
    simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using h
  calc
    (physicalHalfEnergy v).toReal ^ 2 ≤
        (Real.sqrt (physicalEnergy v * criticalGradientEnergy G)) ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).2 hle
    _ = physicalEnergy v * criticalGradientEnergy G := Real.sq_sqrt hnonneg

theorem physicalHalfEnergy_toReal_eq_tsum (v : Field) :
    (physicalHalfEnergy v).toReal = ∑' ki : FourierIndex, physicalHalfEnergyTerm v ki := by
  unfold physicalHalfEnergy
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro ki
  exact ENNReal.toReal_ofReal (physicalHalfEnergyTerm_nonneg v ki)

theorem physicalH1_halfEnergy_summable {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) : Summable (physicalHalfEnergyTerm v) := by
  have h := ENNReal.summable_toReal (physicalH1_halfEnergy_ne_top hv)
  simpa only [ENNReal.toReal_ofReal (physicalHalfEnergyTerm_nonneg v _)] using h

theorem physicalHalfEnergyTerm_of_meanZero (v : Field)
    (hz : SpectralMeanZero (datumFourierCoeff v)) (ki : FourierIndex) :
    physicalHalfEnergyTerm v ki =
      criticalFrequencyWeight ki.1 * Complex.normSq (datumFourierCoeff v ki.1 ki.2) := by
  by_cases hk : ki.1 = 0
  · simp [physicalHalfEnergyTerm, hk, hz ki.2]
  · simp only [physicalHalfEnergyTerm, if_neg hk]

theorem physicalH1_mem_halfSobolev {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G)
    (hz : SpectralMeanZero (datumFourierCoeff v)) :
    Memℓp (criticalWeightedCoeff 1 (datumFourierCoeff v)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  have hterm (ki : FourierIndex) :
      ‖criticalWeightedCoeff 1 (datumFourierCoeff v) ki‖ ^ 2 =
        physicalHalfEnergyTerm v ki := by
    rw [criticalWeightedCoeff_norm, mul_pow, criticalHalfWeight_zpow_sq,
      zpow_one, ← Complex.normSq_eq_norm_sq,
      physicalHalfEnergyTerm_of_meanZero v hz]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hterm] using
    physicalH1_halfEnergy_summable hv

def physicalH1HalfDatum {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    CriticalSobolev 1 :=
  criticalSobolevOfCoeff 1 (datumFourierCoeff v) (physicalH1_mem_halfSobolev hv hz)

@[simp] theorem physicalH1HalfDatum_coeff {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    criticalCoeff 1 (physicalH1HalfDatum hv hz) = datumFourierCoeff v :=
  criticalSobolevOfCoeff_coeff 1 _ _

theorem physicalH1HalfDatum_norm_sq {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    ‖physicalH1HalfDatum hv hz‖ ^ 2 = (physicalHalfEnergy v).toReal := by
  rw [criticalSobolev_norm_sq, physicalH1HalfDatum_coeff,
    physicalHalfEnergy_toReal_eq_tsum]
  apply tsum_congr
  intro ki
  simp only [zpow_one, physicalHalfEnergyTerm_of_meanZero v hz]

/-- Measurability is inherited from the actual physical L2 trajectory. -/
theorem physicalHalfEnergy_aemeasurable
    {α : Type*} [MeasurableSpace α] {m : Measure α} (v : α → Field)
    (hL2 : ∀ᵐ t ∂m, MemLp (v t) 2 (volume.restrict unitCube))
    (hv : AEStronglyMeasurable (fun t => criticalL2Representative (v t)) m) :
    AEMeasurable (fun t => physicalHalfEnergy (v t)) m := by
  have hc (k : Frequency) (i : Fin 3) :
      AEMeasurable (fun t => datumFourierCoeff (v t) k i) m := by
    have h := (criticalCubeFourierFunctional k i).continuous.measurable.comp_aemeasurable
      hv.aemeasurable
    apply h.congr
    filter_upwards [hL2] with t ht
    rw [criticalL2Representative_eq _ ht, criticalCubeFourierFunctional_apply,
      criticalCube_datumFourierCoeff_congr_ae ht.coeFn_toLp]
  unfold physicalHalfEnergy
  apply AEMeasurable.ennreal_tsum
  intro ki
  unfold physicalHalfEnergyTerm
  by_cases hk : ki.1 = 0
  · simp only [if_pos hk]
    exact aemeasurable_const
  · simp only [if_neg hk, Complex.normSq_eq_norm_sq]
    exact (((hc ki.1 ki.2).norm.pow_const 2).const_mul _).ennreal_ofReal

end QuasiFeffermanB
