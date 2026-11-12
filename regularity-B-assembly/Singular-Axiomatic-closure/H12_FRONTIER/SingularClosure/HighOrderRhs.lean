import SingularClosure.HighOrderEstimate
import SingularClosure.SobolevTrajectoryCalculus

/-! Cutoff-independent estimates for the actual Galerkin time derivative in
every Sobolev order. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem highOrderEnergy_leray_le (m N : ℕ) (c : FourierCoeff) :
    highOrderEnergy m N (lerayFourierCoeff c) ≤ highOrderEnergy m N c := by
  unfold highOrderEnergy
  simp_rw [← Finset.mul_sum]
  exact coefficientWeightedEnergy_leray_le N c
    (fun k => torusSobolevWeight k ^ (2 * m))
    (fun k => pow_nonneg (torusSobolevWeight_pos k).le _)

theorem weighted_transport_component_sq_le_tensor
    (m N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c)
    (k : Frequency) (i : Fin 3) :
    (torusSobolevWeight k ^ m * ‖coefficientTransport N c k i‖) ^ 2 ≤
      3 * ∑ j : Fin 3,
        (torusSobolevWeight k ^ (m + 1) * ‖finiteTensorConvolution N c k j i‖) ^ 2 := by
  have hnorm : ‖coefficientTransport N c k i‖ ≤
      ∑ j : Fin 3, ‖derivativeSymbol j k‖ * ‖finiteTensorConvolution N c k j i‖ := by
    rw [coefficientTransport_eq_product_divergence N c hc]
    simpa only [finiteTensorConvolution, finiteScalarConvolution, norm_mul] using
      norm_sum_le Finset.univ (fun j : Fin 3 =>
        derivativeSymbol j k * (∑ p ∈ cutoffModes N, c p j * c (k - p) i))
  have hbound : torusSobolevWeight k ^ m * ‖coefficientTransport N c k i‖ ≤
      ∑ j : Fin 3, torusSobolevWeight k ^ (m + 1) *
        ‖finiteTensorConvolution N c k j i‖ := by
    calc
      _ ≤ torusSobolevWeight k ^ m *
          ∑ j : Fin 3, ‖derivativeSymbol j k‖ * ‖finiteTensorConvolution N c k j i‖ :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (torusSobolevWeight_pos k).le _)
      _ = ∑ j : Fin 3, torusSobolevWeight k ^ m *
          (‖derivativeSymbol j k‖ * ‖finiteTensorConvolution N c k j i‖) :=
        Finset.mul_sum ..
      _ ≤ ∑ j : Fin 3, torusSobolevWeight k ^ m *
          (torusSobolevWeight k * ‖finiteTensorConvolution N c k j i‖) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_weight k j) (norm_nonneg _))
          (pow_nonneg (torusSobolevWeight_pos k).le _)
      _ = _ := by simp only [pow_succ, mul_assoc]
  have hleft : 0 ≤ torusSobolevWeight k ^ m * ‖coefficientTransport N c k i‖ :=
    mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _) (norm_nonneg _)
  have hright : 0 ≤ ∑ j : Fin 3,
      torusSobolevWeight k ^ (m + 1) * ‖finiteTensorConvolution N c k j i‖ :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le _) (norm_nonneg _))
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j : Fin 3 => torusSobolevWeight k ^ (m + 1) *
      ‖finiteTensorConvolution N c k j i‖)
  exact ((sq_le_sq₀ hleft hright).mpr hbound).trans (by simpa using hcs)

theorem highOrderEnergy_transport_le_tensor (m N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) :
    highOrderEnergy m N (coefficientTransport N c) ≤ 3 * highOrderTensorEnergy (m + 1) N c := by
  have hsum := Finset.sum_le_sum (s := cutoffModes N) (fun k hk =>
    Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
      weighted_transport_component_sq_le_tensor m N c hc k i))
  simpa only [highOrderEnergy, highOrderTensorEnergy, mul_pow, ← pow_mul,
    Nat.mul_comm m 2, Complex.normSq_eq_norm_sq, ← Finset.mul_sum] using hsum

theorem laplacianFrequency_sq_weight_le (m : ℕ) (k : Frequency) :
    torusSobolevWeight k ^ (2 * m) * laplacianFrequency k ^ 2 ≤
      torusSobolevWeight k ^ (2 * (m + 2)) := by
  have hfreq : 0 ≤ laplacianFrequency k := by
    unfold laplacianFrequency
    have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
      exact_mod_cast galerkinFreqSq_nonneg k
    exact mul_nonneg (sq_nonneg _) hk
  have hle : laplacianFrequency k ≤ torusSobolevWeight k ^ 2 := by
    rw [torusSobolevWeight_sq]
    unfold laplacianFrequency
    linarith
  calc
    _ ≤ torusSobolevWeight k ^ (2 * m) * (torusSobolevWeight k ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfreq hle 2)
        (pow_nonneg (torusSobolevWeight_pos k).le _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega

theorem highOrderEnergy_galerkinRhs_le (ν : ℝ) (m N : ℕ) (c : FourierCoeff) :
    highOrderEnergy m N (galerkinRhs ν N c) ≤
      2 * ν ^ 2 * highOrderEnergy (m + 2) N c +
        2 * highOrderEnergy m N (coefficientTransport N c) := by
  have hpoint (k : Frequency) (i : Fin 3) :
      torusSobolevWeight k ^ (2 * m) * Complex.normSq (galerkinRhs ν N c k i) ≤
        2 * ν ^ 2 * (torusSobolevWeight k ^ (2 * (m + 2)) * Complex.normSq (c k i)) +
          2 * (torusSobolevWeight k ^ (2 * m) *
            Complex.normSq (coefficientLeray k (coefficientTransport N c k) i)) := by
    have hw := mul_le_mul_of_nonneg_right (laplacianFrequency_sq_weight_le m k)
      (Complex.normSq_nonneg (c k i))
    have hv : torusSobolevWeight k ^ (2 * m) *
        Complex.normSq (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i) ≤
          ν ^ 2 * (torusSobolevWeight k ^ (2 * (m + 2)) * Complex.normSq (c k i)) := by
      rw [normSq_viscous_coefficient]
      have h := mul_le_mul_of_nonneg_left hw (sq_nonneg ν)
      unfold laplacianFrequency at h
      nlinarith
    have h := mul_le_mul_of_nonneg_left
      (complex_normSq_sub_le_twice
        (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i)
        (coefficientLeray k (coefficientTransport N c k) i))
      (pow_nonneg (torusSobolevWeight_pos k).le (2 * m))
    change torusSobolevWeight k ^ (2 * m) * Complex.normSq
      (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i -
        coefficientLeray k (coefficientTransport N c k) i) ≤ _
    nlinarith
  have hproj : highOrderEnergy m N (galerkinRhs ν N c) ≤
      2 * ν ^ 2 * highOrderEnergy (m + 2) N c +
        2 * highOrderEnergy m N (lerayFourierCoeff (coefficientTransport N c)) := by
    have hsum := Finset.sum_le_sum (s := cutoffModes N) (fun k hk =>
      Finset.sum_le_sum (s := Finset.univ) (fun i hi => hpoint k i))
    simpa only [highOrderEnergy, lerayFourierCoeff,
      Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  exact hproj.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (highOrderEnergy_leray_le m N (coefficientTransport N c))
      (by norm_num)))

theorem FINITE_FOURIER_RHS_TAME_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k, k ∉ cutoffModes N → ∀ i, c k i = 0) → SpectralSolenoidal c →
      highOrderEnergy m N (galerkinRhs ν N c) ≤
        2 * ν ^ 2 * highOrderEnergy (m + 2) N c +
          C * highOrderEnergy 2 N c * highOrderEnergy (m + 1) N c := by
  obtain ⟨C, hC, htensor⟩ := FINITE_FOURIER_TENSOR_TAME_BOUND (m + 1)
  refine ⟨6 * C, by positivity, ?_⟩
  intro ν N c hsupp hsol
  have ht := (highOrderEnergy_transport_le_tensor m N c hsol).trans
    (mul_le_mul_of_nonneg_left (htensor N c hsupp) (by norm_num : (0 : ℝ) ≤ 3))
  have hrhs := highOrderEnergy_galerkinRhs_le ν m N c
  nlinarith

theorem GALERKIN_RHS_SOBOLEV_NORM_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t →
      ‖g.rhsSobolev m t‖ ^ 2 ≤
        2 * ν ^ 2 * highOrderEnergy (m + 2) N (g.coeff t) +
          C * highOrderEnergy 2 N (g.coeff t) * highOrderEnergy (m + 1) N (g.coeff t) := by
  obtain ⟨C, hC, hrhs⟩ := FINITE_FOURIER_RHS_TAME_BOUND m
  refine ⟨C, hC, ?_⟩
  intro ν a N g t ht
  rw [g.rhsSobolev_eq_finiteSobolev m t ht,
    ← highOrderEnergy_eq_sobolev_norm_sq]
  exact hrhs ν N (g.coeff t) (g.mode_support t ht) (g.solenoidal t ht)

/-- The derivative in the actual Sobolev Hilbert space has a uniform high-order
bound. The viscosity and nonlinear terms are the literal finite ODE terms. -/
theorem GALERKIN_SOBOLEV_TIME_DERIVATIVE_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t →
      ‖derivWithin (g.sobolevState m) (Ici 0) t‖ ^ 2 ≤
        2 * ν ^ 2 * highOrderEnergy (m + 2) N (g.coeff t) +
          C * highOrderEnergy 2 N (g.coeff t) * highOrderEnergy (m + 1) N (g.coeff t) := by
  obtain ⟨C, hC, hrhs⟩ := GALERKIN_RHS_SOBOLEV_NORM_BOUND m
  refine ⟨C, hC, ?_⟩
  intro ν a N g t ht
  rw [g.sobolevState_derivWithin m t ht]
  exact hrhs ν a N g t ht

end

end SingularClosure
