import QuasiFeffermanB.PhysicalFourierL2

/-! The physical H1 good-time trace is an actual weighted Fourier H1 datum.
The half-order and physical initial states are identified by exact coefficients. -/

set_option autoImplicit false
set_option Elab.async true
noncomputable section
open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ENNReal Topology

namespace QuasiFeffermanB

theorem meanZero_sobolevCutoff_sum (q N : ℕ) (c : FourierCoeff)
    (hz : SpectralMeanZero c) :
    (∑ ki ∈ sobolevCutoffIndices N,
      criticalFrequencyWeight ki.1 ^ q * Complex.normSq (c ki.1 ki.2)) =
      criticalEnergy q N c := by
  classical
  unfold sobolevCutoffIndices
  have hprod :
      (∑ ki ∈ (sobolevCutoffModes N).product (Finset.univ : Finset (Fin 3)),
        criticalFrequencyWeight ki.1 ^ q * Complex.normSq (c ki.1 ki.2)) =
      ∑ k ∈ sobolevCutoffModes N, ∑ i : Fin 3,
        criticalFrequencyWeight k ^ q * Complex.normSq (c k i) :=
    Finset.sum_product _ _ _
  rw [hprod, sobolevCutoffModes, Finset.sum_insert (by
    intro h
    exact ((mem_cutoffModes_iff N 0).mp h).2.1 rfl)]
  have hz0 (i : Fin 3) : c 0 i = 0 := hz i
  simp only [hz0, Complex.normSq_zero, mul_zero, Finset.sum_const_zero, zero_add,
    criticalEnergy]

theorem physicalH1_weighted_finite_bound
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v))
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖criticalWeightedCoeff 2 (datumFourierCoeff v) ki‖ ^ 2) ≤
      criticalGradientEnergy G := by
  classical
  obtain ⟨N, hN⟩ :=
    (sobolevCutoffIndices_tendsto_atTop.eventually (eventually_ge_atTop S)).exists
  have hterm (ki : FourierIndex) :
      ‖criticalWeightedCoeff 2 (datumFourierCoeff v) ki‖ ^ 2 =
        criticalFrequencyWeight ki.1 ^ (2 : ℕ) *
          Complex.normSq (datumFourierCoeff v ki.1 ki.2) := by
    simp only [criticalWeightedCoeff_norm, mul_pow, zpow_ofNat,
      criticalHalfWeight_sq, Complex.normSq_eq_norm_sq]
  calc
    (∑ ki ∈ S, ‖criticalWeightedCoeff 2 (datumFourierCoeff v) ki‖ ^ 2) ≤
        ∑ ki ∈ sobolevCutoffIndices N,
          ‖criticalWeightedCoeff 2 (datumFourierCoeff v) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => sq_nonneg _)
    _ = criticalEnergy 2 N (datumFourierCoeff v) := by
      simp only [hterm]
      exact meanZero_sobolevCutoff_sum 2 N _ hz
    _ = coefficientDissipation N (datumFourierCoeff v) :=
      criticalEnergy_two_eq_coefficientDissipation N _
    _ ≤ criticalGradientEnergy G := (physicalH1_cutoff_bounds hv N).2

theorem physicalH1_mem_sobolevTwo
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    Memℓp (criticalWeightedCoeff 2 (datumFourierCoeff v)) 2 := by
  apply memℓp_gen' (C := criticalGradientEnergy G)
  intro S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    physicalH1_weighted_finite_bound hv hz S

def physicalH1SobolevDatum
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    CriticalSobolev 2 :=
  criticalSobolevOfCoeff 2 (datumFourierCoeff v) (physicalH1_mem_sobolevTwo hv hz)

@[simp] theorem physicalH1SobolevDatum_coeff
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    criticalCoeff 2 (physicalH1SobolevDatum hv hz) = datumFourierCoeff v :=
  criticalSobolevOfCoeff_coeff 2 _ _

theorem physicalH1SobolevDatum_lower_half
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    criticalSobolevLower 1 2 (by norm_num) (physicalH1SobolevDatum hv hz) =
      physicalH1HalfDatum hv hz := by
  apply criticalCoeff_injective 1
  rw [criticalSobolevLower_coeff, physicalH1SobolevDatum_coeff, physicalH1HalfDatum_coeff]

theorem physicalH1SobolevDatum_half_norm_sq
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    ‖criticalSobolevLower 1 2 (by norm_num) (physicalH1SobolevDatum hv hz)‖ ^ 2 =
      (physicalHalfEnergy v).toReal := by
  rw [physicalH1SobolevDatum_lower_half, physicalH1HalfDatum_norm_sq]

theorem physicalH1SobolevDatum_physicalL2
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G) (hz : SpectralMeanZero (datumFourierCoeff v)) :
    criticalInitialPhysicalL2
      (criticalSobolevLower 1 2 (by norm_num) (physicalH1SobolevDatum hv hz)) =
        criticalL2Representative v := by
  rw [physicalH1SobolevDatum_lower_half, physicalH1HalfDatum_physicalL2,
    criticalL2Representative_eq _ hv.velocity_L2]

end QuasiFeffermanB
