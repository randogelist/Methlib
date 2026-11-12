import SingularityDisprovement.DyadicArithmetic
import SingularClosure.CriticalRegularityContracts

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators Topology
open SingularClosure

namespace SingularityDisprovement

noncomputable section

def shearFrequency (z : ℤ) : Frequency := ![0, z, 0]

@[simp] theorem shearFrequency_zero : shearFrequency 0 = 0 := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem shearFrequency_apply_zero (z : ℤ) : shearFrequency z 0 = 0 := rfl
@[simp] theorem shearFrequency_apply_one (z : ℤ) : shearFrequency z 1 = z := rfl
@[simp] theorem shearFrequency_apply_two (z : ℤ) : shearFrequency z 2 = 0 := rfl

theorem shearFrequency_injective : Function.Injective shearFrequency := by
  intro z w h
  exact congrArg (fun k : Frequency => k 1) h

theorem shearFrequency_ne_zero {z : ℤ} (hz : z ≠ 0) : shearFrequency z ≠ 0 := by
  intro h
  apply hz
  have h' := congrArg (fun k : Frequency => k 1) h
  simpa using h'

theorem shearFrequency_of_axis {k : Frequency} (h0 : k 0 = 0) (h2 : k 2 = 0) :
    shearFrequency (k 1) = k := by
  ext i
  fin_cases i <;> simp [h0, h2]

def shearFourierIndex (z : ℤ) : FourierIndex := (shearFrequency z, 0)

theorem shearFourierIndex_injective : Function.Injective shearFourierIndex := by
  intro z w h
  exact shearFrequency_injective (congrArg Prod.fst h)

def dyadicCoeff (ν : ℝ) : FourierCoeff := fun k i =>
  if i = 0 ∧ k 0 = 0 ∧ k 2 = 0 then ((ν / 4 * dyadicAmplitude (k 1).natAbs : ℝ) : ℂ)
  else 0

@[simp] theorem dyadicCoeff_axis (ν : ℝ) (z : ℤ) :
    dyadicCoeff ν (shearFrequency z) 0 =
      ((ν / 4 * dyadicAmplitude z.natAbs : ℝ) : ℂ) := by
  simp [dyadicCoeff]

theorem dyadicCoeff_reality (ν : ℝ) : SpectralReality (dyadicCoeff ν) := by
  intro k i
  by_cases h : i = 0 ∧ k 0 = 0 ∧ k 2 = 0
  · simp [dyadicCoeff, h, Pi.neg_apply]
  · have h' : ¬ (i = 0 ∧ (-k) 0 = 0 ∧ (-k) 2 = 0) := by
      simpa using h
    simp [dyadicCoeff, h, h']

theorem dyadicCoeff_mean_zero (ν : ℝ) : SpectralMeanZero (dyadicCoeff ν) := by
  intro i
  simp [dyadicCoeff]

theorem dyadicCoeff_solenoidal (ν : ℝ) : SpectralSolenoidal (dyadicCoeff ν) := by
  intro k
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : i = 0 ∧ k 0 = 0 ∧ k 2 = 0
  · simp [dyadicCoeff, h, h.1, h.2.1]
  · simp [dyadicCoeff, h]

theorem criticalFrequencyWeight_shear {z : ℤ} (hz : z ≠ 0) :
    criticalFrequencyWeight (shearFrequency z) = 2 * Real.pi * (z.natAbs : ℝ) := by
  have hsq := criticalFrequencyWeight_sq_of_ne_zero (shearFrequency z)
    (shearFrequency_ne_zero hz)
  have habs : ((z.natAbs : ℕ) : ℝ) ^ 2 = (z : ℝ) ^ 2 := by
    norm_cast
    exact_mod_cast Int.natAbs_sq z
  have hs : laplacianFrequency (shearFrequency z) =
      (2 * Real.pi) ^ 2 * (z : ℝ) ^ 2 := by
    simp [laplacianFrequency, galerkinFreqSq, Fin.sum_univ_succ, shearFrequency]
  rw [hs] at hsq
  have hp := criticalFrequencyWeight_pos (shearFrequency z)
  have hq : 0 ≤ 2 * Real.pi * (z.natAbs : ℝ) := by positivity
  nlinarith

theorem dyadicCoeff_weighted_axis_sq (ν : ℝ) (z : ℤ) :
    ‖criticalWeightedCoeff 1 (dyadicCoeff ν) (shearFourierIndex z)‖ ^ 2 =
      (2 * Real.pi * (ν / 4) ^ 2) * ((z.natAbs : ℝ) * dyadicAmplitude z.natAbs ^ 2) := by
  by_cases hz : z = 0
  · subst z
    simp [criticalWeightedCoeff, shearFourierIndex, dyadicCoeff]
  · rw [criticalWeightedCoeff_norm]
    simp only [shearFourierIndex, zpow_one, mul_pow, criticalHalfWeight_sq,
      dyadicCoeff_axis, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [criticalFrequencyWeight_shear hz]
    ring

theorem dyadicCoeff_weighted_summable (ν : ℝ) :
    Summable (fun ki : FourierIndex => ‖criticalWeightedCoeff 1 (dyadicCoeff ν) ki‖ ^ 2) := by
  apply (shearFourierIndex_injective.summable_iff ?_).mp
  · have hz : Summable (fun z : ℤ =>
        (z.natAbs : ℝ) * dyadicAmplitude z.natAbs ^ 2) := by
      apply Summable.of_nat_of_neg
      · simpa using dyadicAmplitude_weighted_sq_summable
      · simpa using dyadicAmplitude_weighted_sq_summable
    convert hz.mul_left (2 * Real.pi * (ν / 4) ^ 2) using 1
    ext z
    exact dyadicCoeff_weighted_axis_sq ν z
  · intro ki hki
    have h : ¬ (ki.2 = 0 ∧ ki.1 0 = 0 ∧ ki.1 2 = 0) := by
      intro h
      apply hki
      refine ⟨ki.1 1, ?_⟩
      apply Prod.ext
      · exact shearFrequency_of_axis h.2.1 h.2.2
      · exact h.1.symm
    simp [criticalWeightedCoeff, dyadicCoeff, h]

theorem dyadicCoeff_mem (ν : ℝ) : Memℓp (criticalWeightedCoeff 1 (dyadicCoeff ν)) 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using dyadicCoeff_weighted_summable ν

/-- Actual native critical datum; membership is proved by the exact weighted series. -/
def dyadicSeed (ν : ℝ) : CriticalSobolev 1 :=
  criticalSobolevOfCoeff 1 (dyadicCoeff ν) (dyadicCoeff_mem ν)

@[simp] theorem dyadicSeed_coeff (ν : ℝ) :
    criticalCoeff 1 (dyadicSeed ν) = dyadicCoeff ν := by
  exact criticalSobolevOfCoeff_coeff _ _ _

theorem dyadicSeed_sigma (ν : ℝ) : CriticalSigmaZero (dyadicSeed ν) := by
  constructor
  · simpa using dyadicCoeff_reality ν
  · simpa using dyadicCoeff_solenoidal ν
  · simpa using dyadicCoeff_mean_zero ν

theorem dyadicSeed_norm_pos {ν : ℝ} (hν : 0 < ν) : 0 < ‖dyadicSeed ν‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hc := congrArg (fun a : CriticalSobolev 1 =>
    criticalCoeff 1 a (shearFrequency 2) 0) h
  have hν0 : ν ≠ 0 := ne_of_gt hν
  simpa [dyadicSeed_coeff, dyadicCoeff_axis, hν0] using hc

end
end SingularityDisprovement
