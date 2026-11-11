import SingularClosure.HighOrderProduct
import SingularClosure.HighOrderGalerkin

/-! Cutoff-independent tame estimates for the actual Galerkin nonlinear power. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

def highOrderComponentEnergy (m N : ℕ) (c : FourierCoeff) (i : Fin 3) : ℝ :=
  ∑ k ∈ cutoffModes N, (torusSobolevWeight k ^ m * ‖c k i‖) ^ 2

def finiteTensorConvolution (N : ℕ) (c : FourierCoeff)
    (k : Frequency) (j i : Fin 3) : ℂ :=
  finiteScalarConvolution (cutoffModes N) (fun p => c p j) (fun q => c q i) k

def highOrderTensorEnergy (m N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3, ∑ j : Fin 3,
    (torusSobolevWeight k ^ m * ‖finiteTensorConvolution N c k j i‖) ^ 2

theorem highOrderComponentEnergy_nonneg (m N : ℕ) (c : FourierCoeff) (i : Fin 3) :
    0 ≤ highOrderComponentEnergy m N c i :=
  Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem highOrderEnergy_eq_sum_components (m N : ℕ) (c : FourierCoeff) :
    highOrderEnergy m N c = ∑ i : Fin 3, highOrderComponentEnergy m N c i := by
  unfold highOrderEnergy highOrderComponentEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow, ← pow_mul, Nat.mul_comm m 2, Complex.normSq_eq_norm_sq]

theorem FINITE_FOURIER_TENSOR_TAME_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k, k ∉ cutoffModes N → ∀ i, c k i = 0) →
      highOrderTensorEnergy m N c ≤ C * highOrderEnergy 2 N c * highOrderEnergy m N c := by
  obtain ⟨C, hC, hprod⟩ := FINITE_FOURIER_TAME_PRODUCT_BOUND m
  refine ⟨2 * C, by positivity, ?_⟩
  intro N c hsupp
  have hpair (i j : Fin 3) :
      (∑ k ∈ cutoffModes N,
        (torusSobolevWeight k ^ m * ‖finiteTensorConvolution N c k j i‖) ^ 2) ≤
      C * (highOrderComponentEnergy 2 N c i * highOrderComponentEnergy m N c j +
        highOrderComponentEnergy 2 N c j * highOrderComponentEnergy m N c i) :=
    hprod (cutoffModes N) (cutoffModes N) (cutoffModes N)
      (fun p => c p j) (fun q => c q i) (fun k hk => hsupp k hk i)
  calc
    highOrderTensorEnergy m N c = ∑ i : Fin 3, ∑ j : Fin 3,
        ∑ k ∈ cutoffModes N,
          (torusSobolevWeight k ^ m * ‖finiteTensorConvolution N c k j i‖) ^ 2 := by
      unfold highOrderTensorEnergy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        C * (highOrderComponentEnergy 2 N c i * highOrderComponentEnergy m N c j +
          highOrderComponentEnergy 2 N c j * highOrderComponentEnergy m N c i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => hpair i j)
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [← highOrderEnergy_eq_sum_components]
      ring

theorem derivativeSymbol_norm_le_weight (k : Frequency) (j : Fin 3) :
    ‖derivativeSymbol j k‖ ≤ torusSobolevWeight k := by
  have hn : ‖derivativeSymbol j k‖ ^ 2 = (2 * Real.pi * (k j : ℝ)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [derivativeSymbol, Complex.normSq_apply, pow_two]
  have hs : (2 * Real.pi * (k j : ℝ)) ^ 2 ≤ laplacianFrequency k := by
    rw [← sum_derivativeScale_sq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  apply (sq_le_sq₀ (norm_nonneg _) (torusSobolevWeight_pos k).le).mp
  rw [hn, torusSobolevWeight_sq]
  unfold laplacianFrequency at hs
  linarith

theorem highOrderNonlinearPower_eq_triple_sum (m N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) :
    highOrderNonlinearPower m N c =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3, ∑ j : Fin 3,
        torusSobolevWeight k ^ (2 * m) *
          (star (c k i) * (derivativeSymbol j k * finiteTensorConvolution N c k j i)).re := by
  rw [highOrderNonlinearPower_eq_transport m N c hc]
  simp_rw [coefficientTransport_eq_product_divergence N c hc]
  simp only [finiteTensorConvolution, finiteScalarConvolution, Finset.mul_sum, Complex.re_sum]

theorem highOrder_triple_term_abs_le (m N : ℕ) (c : FourierCoeff)
    (k : Frequency) (i j : Fin 3) :
    abs (torusSobolevWeight k ^ (2 * m) *
      (star (c k i) * (derivativeSymbol j k * finiteTensorConvolution N c k j i)).re) ≤
        (torusSobolevWeight k ^ (m + 1) * ‖c k i‖) *
          (torusSobolevWeight k ^ m * ‖finiteTensorConvolution N c k j i‖) := by
  have hw : 0 ≤ torusSobolevWeight k ^ (2 * m) :=
    pow_nonneg (torusSobolevWeight_pos k).le _
  rw [abs_mul, abs_of_nonneg hw]
  calc
    _ ≤ torusSobolevWeight k ^ (2 * m) *
        ‖star (c k i) * (derivativeSymbol j k * finiteTensorConvolution N c k j i)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hw
    _ = torusSobolevWeight k ^ (2 * m) *
        (‖c k i‖ * (‖derivativeSymbol j k‖ * ‖finiteTensorConvolution N c k j i‖)) := by
      rw [norm_mul, norm_mul, norm_star]
    _ ≤ torusSobolevWeight k ^ (2 * m) *
        (‖c k i‖ * (torusSobolevWeight k * ‖finiteTensorConvolution N c k j i‖)) := by
      apply mul_le_mul_of_nonneg_left _ hw
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_weight k j) (norm_nonneg _)
    _ = _ := by
      have hpow : torusSobolevWeight k ^ (2 * m) * torusSobolevWeight k =
          torusSobolevWeight k ^ (m + 1) * torusSobolevWeight k ^ m := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      calc
        _ = (torusSobolevWeight k ^ (2 * m) * torusSobolevWeight k) *
            (‖c k i‖ * ‖finiteTensorConvolution N c k j i‖) := by ring
        _ = _ := by rw [hpow]; ring

theorem highOrderNonlinearPower_sq_le_tensor (m N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) :
    highOrderNonlinearPower m N c ^ 2 ≤
      3 * highOrderEnergy (m + 1) N c * highOrderTensorEnergy m N c := by
  let s : Finset (Frequency × (Fin 3 × Fin 3)) :=
    (cutoffModes N).product (Finset.univ.product Finset.univ)
  let A : Frequency × (Fin 3 × Fin 3) → ℝ :=
    fun z => torusSobolevWeight z.1 ^ (m + 1) * ‖c z.1 z.2.1‖
  let B : Frequency × (Fin 3 × Fin 3) → ℝ :=
    fun z => torusSobolevWeight z.1 ^ m *
      ‖finiteTensorConvolution N c z.1 z.2.2 z.2.1‖
  let T : Frequency × (Fin 3 × Fin 3) → ℝ :=
    fun z => torusSobolevWeight z.1 ^ (2 * m) *
      (star (c z.1 z.2.1) *
        (derivativeSymbol z.2.2 z.1 * finiteTensorConvolution N c z.1 z.2.2 z.2.1)).re
  have hp : highOrderNonlinearPower m N c = ∑ z ∈ s, T z := by
    simpa only [s, T, Finset.sum_product] using
      highOrderNonlinearPower_eq_triple_sum m N c hc
  have hbound : abs (highOrderNonlinearPower m N c) ≤ ∑ z ∈ s, A z * B z := by
    rw [hp]
    apply (Finset.abs_sum_le_sum_abs T s).trans
    apply Finset.sum_le_sum
    intro z _
    exact highOrder_triple_term_abs_le m N c z.1 z.2.1 z.2.2
  have hab : 0 ≤ ∑ z ∈ s, A z * B z := by
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (torusSobolevWeight_pos z.1).le _) (norm_nonneg _))
      (mul_nonneg (pow_nonneg (torusSobolevWeight_pos z.1).le _) (norm_nonneg _))
  have he : (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      (torusSobolevWeight k ^ (m + 1) * ‖c k i‖) ^ 2) =
        highOrderEnergy (m + 1) N c := by
    unfold highOrderEnergy
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, ← pow_mul, Nat.mul_comm (m + 1) 2, Complex.normSq_eq_norm_sq]
  have ha : (∑ z ∈ s, A z ^ 2) = 3 * highOrderEnergy (m + 1) N c := by
    simp only [s, A, Finset.sum_product, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp_rw [← Finset.mul_sum]
    rw [he]
  have hb : (∑ z ∈ s, B z ^ 2) = highOrderTensorEnergy m N c := by
    simp only [s, B, Finset.sum_product, highOrderTensorEnergy]
  calc
    highOrderNonlinearPower m N c ^ 2 = abs (highOrderNonlinearPower m N c) ^ 2 :=
      (sq_abs _).symm
    _ ≤ (∑ z ∈ s, A z * B z) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hab).mpr hbound
    _ ≤ (∑ z ∈ s, A z ^ 2) * ∑ z ∈ s, B z ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s A B
    _ = _ := by rw [ha, hb]

theorem FINITE_FOURIER_NONLINEAR_POWER_TAME_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k, k ∉ cutoffModes N → ∀ i, c k i = 0) → SpectralSolenoidal c →
      highOrderNonlinearPower m N c ^ 2 ≤
        C * highOrderEnergy (m + 1) N c * highOrderEnergy 2 N c * highOrderEnergy m N c := by
  obtain ⟨C, hC, htensor⟩ := FINITE_FOURIER_TENSOR_TAME_BOUND m
  refine ⟨3 * C, by positivity, ?_⟩
  intro N c hsupp hsol
  calc
    _ ≤ 3 * highOrderEnergy (m + 1) N c * highOrderTensorEnergy m N c :=
      highOrderNonlinearPower_sq_le_tensor m N c hsol
    _ ≤ 3 * highOrderEnergy (m + 1) N c *
        (C * highOrderEnergy 2 N c * highOrderEnergy m N c) :=
      mul_le_mul_of_nonneg_left (htensor N c hsupp)
        (mul_nonneg (by norm_num) (highOrderEnergy_nonneg _ _ _))
    _ = _ := by ring

/-- Every Sobolev order obeys the same linear-in-energy estimate, with its
coefficient determined by the actual order-two Galerkin energy. -/
theorem GALERKIN_HIGH_ORDER_DIFFERENTIAL_INEQUALITY (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t → ∃ d : ℝ,
        HasDerivWithinAt (fun r => highOrderEnergy m N (g.coeff r)) d (Ici 0) t ∧
        d + ν * highOrderEnergy (m + 1) N (g.coeff t) ≤
          (2 * ν + C / ν * highOrderEnergy 2 N (g.coeff t)) *
            highOrderEnergy m N (g.coeff t) := by
  obtain ⟨C, hC, hpower⟩ := FINITE_FOURIER_NONLINEAR_POWER_TAME_BOUND m
  refine ⟨C, hC, ?_⟩
  intro ν hν a N g t ht
  refine ⟨(-2 * ν) *
      (highOrderEnergy (m + 1) N (g.coeff t) - highOrderEnergy m N (g.coeff t)) -
      2 * highOrderNonlinearPower m N (g.coeff t),
    g.highOrderEnergy_balance m ht, ?_⟩
  have hp := hpower N (g.coeff t) (g.mode_support t ht) (g.solenoidal t ht)
  have hsquare : abs (highOrderNonlinearPower m N (g.coeff t)) ^ 2 ≤
      (ν * highOrderEnergy (m + 1) N (g.coeff t)) *
        (C / ν * highOrderEnergy 2 N (g.coeff t) * highOrderEnergy m N (g.coeff t)) := by
    rw [sq_abs]
    calc
      _ ≤ C * highOrderEnergy (m + 1) N (g.coeff t) *
          highOrderEnergy 2 N (g.coeff t) * highOrderEnergy m N (g.coeff t) := hp
      _ = _ := by field_simp [ne_of_gt hν] <;> ring
  have habs := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hν.le (highOrderEnergy_nonneg (m + 1) N (g.coeff t)))
    (mul_nonneg (mul_nonneg (div_nonneg hC.le hν.le)
      (highOrderEnergy_nonneg 2 N (g.coeff t)))
      (highOrderEnergy_nonneg m N (g.coeff t))) hsquare
  have hneg := neg_le_abs (highOrderNonlinearPower m N (g.coeff t))
  nlinarith

end

end SingularClosure
