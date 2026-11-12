import SingularClosure.CriticalFourierInterpolation
import SingularClosure.PhysicalBilinear

/-!
# Actual finite homogeneous Fourier energy balances

The exponent q denotes twice the homogeneous Sobolev order. Every balance
below differentiates the original finite coefficient ODE. The q = 1
nonlinear power is identified with the actual physical pairing against Λu.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

def criticalNonlinearPower (q N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    criticalFrequencyWeight k ^ q *
      (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re

def criticalEnergyRate (ν : ℝ) (q N : ℕ) (c : FourierCoeff) : ℝ :=
  (-2 * ν) * criticalEnergy (q + 2) N c - 2 * criticalNonlinearPower q N c

theorem criticalFrequencyWeight_sq_of_cutoff
    {N : ℕ} {k : Frequency} (hk : k ∈ cutoffModes N) :
    criticalFrequencyWeight k ^ 2 = laplacianFrequency k := by
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  have hfreq : 0 ≤ laplacianFrequency k := by
    unfold laplacianFrequency
    exact mul_nonneg (sq_nonneg _) (by exact_mod_cast galerkinFreqSq_nonneg k)
  rw [criticalFrequencyWeight, if_neg hk0, Real.sq_sqrt hfreq]

theorem criticalEnergy_rate_split (ν : ℝ) (q N : ℕ) (c : FourierCoeff) :
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      criticalFrequencyWeight k ^ q *
        (2 * (star (c k i) * galerkinRhs ν N c k i).re)) =
      criticalEnergyRate ν q N c := by
  have hpoint (k : Frequency) (hk : k ∈ cutoffModes N) (i : Fin 3) :
      criticalFrequencyWeight k ^ q *
          (2 * (star (c k i) * galerkinRhs ν N c k i).re) =
        (-2 * ν) *
          (criticalFrequencyWeight k ^ (q + 2) * Complex.normSq (c k i)) -
        2 * (criticalFrequencyWeight k ^ q *
          (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re) := by
    rw [galerkinRhs, complex_viscous_pairing, pow_add,
      criticalFrequencyWeight_sq_of_cutoff hk]
    unfold laplacianFrequency
    ring
  unfold criticalEnergyRate criticalEnergy criticalNonlinearPower
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hpoint k hk i)

/-- A coefficient-curve form, independent of the representation of initial data. -/
theorem criticalEnergy_hasDerivWithinAt
    {ν t : ℝ} {N : ℕ} {c : ℝ → FourierCoeff} {s : Set ℝ}
    (q : ℕ)
    (heq : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i) (galerkinRhs ν N (c t) k i) s t) :
    HasDerivWithinAt (fun r => criticalEnergy q N (c r))
      (criticalEnergyRate ν q N (c t)) s t := by
  rw [← criticalEnergy_rate_split]
  unfold criticalEnergy
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i _
  exact (hasDerivWithinAt_complex_normSq (heq k hk i)).const_mul _

theorem GalerkinSolution.criticalEnergy_balance
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => criticalEnergy q N (g.coeff r))
      (criticalEnergyRate ν q N (g.coeff t)) (Ici 0) t :=
  criticalEnergy_hasDerivWithinAt q (g.equation t ht)

theorem GalerkinSolution.criticalEnergy_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (q : ℕ) :
    ContinuousOn (fun t => criticalEnergy q N (g.coeff t)) (Ici 0) := by
  intro t ht
  exact (g.criticalEnergy_balance q ht).continuousWithinAt

theorem criticalNonlinearPower_eq_transport
    (q N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c) :
    criticalNonlinearPower q N c =
      ∑ k ∈ cutoffModes N, criticalFrequencyWeight k ^ q *
        (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re := by
  unfold criticalNonlinearPower
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum, ← Complex.re_sum,
    coefficientLeray_pairing k (c k) (coefficientTransport N c k) (hc k)]

/-- The actual finite Λ multiplier. Its zero value is immaterial because
the finite synthesis excludes the zero frequency. -/
def criticalLambdaCoefficient (c : FourierCoeff) : FourierCoeff :=
  fun k i => (criticalFrequencyWeight k : ℂ) * c k i

theorem criticalFrequencyWeight_neg (k : Frequency) :
    criticalFrequencyWeight (-k) = criticalFrequencyWeight k := by
  simp [criticalFrequencyWeight, laplacianFrequency, galerkinFreqSq]

theorem criticalLambdaCoefficient_reality (c : FourierCoeff) (hc : SpectralReality c) :
    SpectralReality (criticalLambdaCoefficient c) := by
  intro k i
  simp [criticalLambdaCoefficient, criticalFrequencyWeight_neg, hc k i, Complex.star_def]

theorem criticalLambdaCoefficient_energy (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N (criticalLambdaCoefficient c) = criticalEnergy 2 N c := by
  unfold coefficientEnergy criticalEnergy
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  simp [criticalLambdaCoefficient, Complex.normSq_mul, Complex.normSq_apply, pow_two]
  <;> ring

/-- Exact L² norm of the actual Λu_N field. -/
theorem FINITE_CRITICAL_LAMBDA_PARSEVAL (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    (∫ x in unitCube, ‖finiteSynthesis N (criticalLambdaCoefficient c) x‖ ^ 2) =
      criticalEnergy 2 N c := by
  rw [← physicalEnergy_eq_integral_norm_sq,
    FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (criticalLambdaCoefficient_reality c hreal),
    criticalLambdaCoefficient_energy]

/-- The critical nonlinear power is the literal physical pairing. -/
theorem criticalNonlinearPower_one_eq_physical
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    criticalNonlinearPower 1 N c =
      ∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (finiteSynthesis N (criticalLambdaCoefficient c) x) := by
  have hswap :
      (∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (finiteSynthesis N (criticalLambdaCoefficient c) x)) =
      ∫ x in unitCube, inner ℝ (finiteSynthesis N (criticalLambdaCoefficient c) x)
        (convection (finiteSynthesis N c) x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact real_inner_comm _ _
  rw [hswap, integral_finiteSynthesis_pairing N (criticalLambdaCoefficient c) _
    (convection_continuous (finiteSynthesis_contDiff N c)),
    datumFourierCoeff_convection_finiteSynthesis N c hsupp hreal,
    criticalNonlinearPower_eq_transport 1 N c hsol]
  apply Finset.sum_congr rfl
  intro k _
  rw [physical_complex_re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [criticalLambdaCoefficient, Complex.star_def, Complex.mul_re, Complex.mul_im]
  <;> ring

/-- Squared homogeneous norms of coordinate derivatives add to the norm
two exponents higher. This is the exact tensor norm needed for L³ control. -/
theorem criticalEnergy_derivative_sum (q N : ℕ) (c : FourierCoeff) :
    (∑ j : Fin 3, criticalEnergy q N (spectralMultiplier (derivativeSymbol j) c)) =
      criticalEnergy (q + 2) N c := by
  have hpoint (k : Frequency) (hk : k ∈ cutoffModes N) (i : Fin 3) :
      (∑ j : Fin 3, criticalFrequencyWeight k ^ q *
        Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i)) =
      criticalFrequencyWeight k ^ (q + 2) * Complex.normSq (c k i) := by
    simp_rw [normSq_derivativeMultiplier]
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_derivativeScale_sq,
      pow_add, criticalFrequencyWeight_sq_of_cutoff hk]
    ring
  unfold criticalEnergy
  calc
    _ = ∑ k ∈ cutoffModes N, ∑ j : Fin 3, ∑ i : Fin 3,
        criticalFrequencyWeight k ^ q *
          Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i) :=
      Finset.sum_comm
    _ = ∑ k ∈ cutoffModes N, ∑ i : Fin 3, ∑ j : Fin 3,
        criticalFrequencyWeight k ^ q *
          Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_congr rfl (fun i _ => hpoint k hk i)

end SingularClosure
