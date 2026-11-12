import SingularClosure.TorusGalerkinSobolev

/-!
# Exact finite Galerkin balances in every Sobolev order

These are identities for the original coefficient ODE and its actual Sobolev
weights. No high-order nonlinear estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

def highOrderEnergy (m N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    torusSobolevWeight k ^ (2 * m) * Complex.normSq (c k i)

def highOrderDissipation (m N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    torusSobolevWeight k ^ (2 * m) *
      ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * Complex.normSq (c k i)

def highOrderNonlinearPower (m N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    torusSobolevWeight k ^ (2 * m) *
      (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re

theorem highOrderEnergy_nonneg (m N : ℕ) (c : FourierCoeff) :
    0 ≤ highOrderEnergy m N c := by
  unfold highOrderEnergy
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _) (sq_nonneg _)

theorem highOrderDissipation_nonneg (m N : ℕ) (c : FourierCoeff) :
    0 ≤ highOrderDissipation m N c := by
  unfold highOrderDissipation
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _)
      (mul_nonneg (sq_nonneg _) hk)) (sq_nonneg _)

theorem highOrderEnergy_eq_sobolev_norm_sq (m N : ℕ) (c : FourierCoeff) :
    highOrderEnergy m N c = ‖finiteSobolev m N c‖ ^ 2 := by
  rw [finiteSobolev_norm_sq]
  unfold highOrderEnergy
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_mul, torusSobolevWeight_sq]

theorem highOrderDissipation_eq_energy_gap (m N : ℕ) (c : FourierCoeff) :
    highOrderDissipation m N c = highOrderEnergy (m + 1) N c - highOrderEnergy m N c := by
  have hweight (k : Frequency) :
      torusSobolevWeight k ^ (2 * (m + 1)) =
        torusSobolevWeight k ^ (2 * m) *
          (1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, torusSobolevWeight_sq]
  have hterm (k : Frequency) (i : Fin 3) :
      torusSobolevWeight k ^ (2 * m) *
          ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * Complex.normSq (c k i) =
        torusSobolevWeight k ^ (2 * (m + 1)) * Complex.normSq (c k i) -
          torusSobolevWeight k ^ (2 * m) * Complex.normSq (c k i) := by
    rw [hweight]
    ring
  simp only [highOrderDissipation, hterm, highOrderEnergy, Finset.sum_sub_distrib]

theorem highOrderEnergy_le_succ (m N : ℕ) (c : FourierCoeff) :
    highOrderEnergy m N c ≤ highOrderEnergy (m + 1) N c := by
  have h := highOrderDissipation_nonneg m N c
  rw [highOrderDissipation_eq_energy_gap] at h
  exact sub_nonneg.mp h

theorem GalerkinSolution.highOrderEnergy_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => highOrderEnergy m N (g.coeff r))
      (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        torusSobolevWeight k ^ (2 * m) *
          (2 * (star (g.coeff t k i) * galerkinRhs ν N (g.coeff t) k i).re))
      (Ici 0) t := by
  unfold highOrderEnergy
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i _
  exact (hasDerivWithinAt_complex_normSq (g.equation t ht k hk i)).const_mul _

theorem highOrderEnergy_rate_split (ν : ℝ) (m N : ℕ) (c : FourierCoeff) :
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      torusSobolevWeight k ^ (2 * m) *
        (2 * (star (c k i) * galerkinRhs ν N c k i).re)) =
      (-2 * ν) * highOrderDissipation m N c - 2 * highOrderNonlinearPower m N c := by
  have hpoint (k : Frequency) (i : Fin 3) :
      torusSobolevWeight k ^ (2 * m) *
          (2 * (star (c k i) * galerkinRhs ν N c k i).re) =
        (-2 * ν) * (torusSobolevWeight k ^ (2 * m) *
          ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * Complex.normSq (c k i)) -
          2 * (torusSobolevWeight k ^ (2 * m) *
            (star (c k i) * coefficientLeray k (coefficientTransport N c k) i).re) := by
    rw [galerkinRhs, complex_viscous_pairing]
    ring
  simp only [hpoint, highOrderDissipation, highOrderNonlinearPower,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact balance in every integral Sobolev order for the actual finite ODE. -/
theorem GalerkinSolution.highOrderEnergy_balance
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => highOrderEnergy m N (g.coeff r))
      ((-2 * ν) *
          (highOrderEnergy (m + 1) N (g.coeff t) - highOrderEnergy m N (g.coeff t)) -
        2 * highOrderNonlinearPower m N (g.coeff t)) (Ici 0) t := by
  rw [← highOrderDissipation_eq_energy_gap, ← highOrderEnergy_rate_split]
  exact g.highOrderEnergy_hasDerivWithinAt m ht

theorem GalerkinSolution.highOrderEnergy_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (m : ℕ) :
    ContinuousOn (fun t => highOrderEnergy m N (g.coeff t)) (Ici 0) := by
  intro t ht
  exact (g.highOrderEnergy_balance m ht).continuousWithinAt

/-- The same derivative is the derivative of the actual Fourier Sobolev norm. -/
theorem GalerkinSolution.sobolevNormSq_balance
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => ‖g.sobolevState m r‖ ^ 2)
      ((-2 * ν) * (‖g.sobolevState (m + 1) t‖ ^ 2 - ‖g.sobolevState m t‖ ^ 2) -
        2 * highOrderNonlinearPower m N (g.coeff t)) (Ici 0) t := by
  simpa only [highOrderEnergy_eq_sobolev_norm_sq, GalerkinSolution.sobolevState] using
    g.highOrderEnergy_balance m ht

theorem highOrderNonlinearPower_eq_transport
    (m N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c) :
    highOrderNonlinearPower m N c =
      ∑ k ∈ cutoffModes N, torusSobolevWeight k ^ (2 * m) *
        (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re := by
  unfold highOrderNonlinearPower
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum, ← Complex.re_sum,
    coefficientLeray_pairing k (c k) (coefficientTransport N c k) (hc k)]

/-- Solenoidality puts the transport derivative on the output frequency,
so the nonlinear term is the divergence of the actual finite Fourier product. -/
theorem coefficientTransport_eq_product_divergence
    (N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c)
    (k : Frequency) (i : Fin 3) :
    coefficientTransport N c k i =
      ∑ j : Fin 3, derivativeSymbol j k *
        (∑ p ∈ cutoffModes N, c p j * c (k - p) i) := by
  have hfreq (p : Frequency) :
      (∑ j : Fin 3, c p j *
        (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
        ∑ j : Fin 3, derivativeSymbol j k * c p j := by
    calc
      _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          transportFrequencyPairing c p (k - p) := by
        unfold transportFrequencyPairing
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.sub_apply]
        push_cast
        ring
      _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * transportFrequencyPairing c p k := by
        rw [transportFrequencyPairing_sub, transportFrequencyPairing_self c p (hc p), sub_zero]
      _ = _ := by
        unfold transportFrequencyPairing
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        unfold derivativeSymbol
        push_cast
        ring
  unfold coefficientTransport
  simp_rw [hfreq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

end

end SingularClosure
