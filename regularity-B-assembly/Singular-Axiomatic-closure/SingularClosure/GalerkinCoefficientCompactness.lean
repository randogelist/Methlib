import SingularClosure.StrongTimeBounds

/-!
# Concrete time modulus of the actual Galerkin Fourier coefficients

The coefficient equation, the fundamental theorem of calculus, and the integral
Cauchy--Schwarz inequality give a squared one-half-Hölder modulus. The energy
of each coefficient derivative is bounded by the actual physical L² energy of
the time derivative. AX6 then makes the modulus uniform in the cutoff.

This module supplies temporal equicontinuity, not the full strong-limit theorem.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators Interval

namespace SingularClosure

noncomputable section

/-- Integral Cauchy--Schwarz against the constant function, proved by a square. -/
theorem intervalIntegral_sq_le_length_mul_integral_sq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∫ r in a..b, f r) ^ 2 ≤ (b - a) * (∫ r in a..b, (f r) ^ 2) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  let L : ℝ := b - a
  let A : ℝ := ∫ r in a..b, f r
  have hL : 0 < L := sub_pos.mpr hlt
  have hi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun r => f r ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab
  have hnonneg : 0 ≤ ∫ r in a..b, (L * f r - A) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun r => sq_nonneg _)
  have hpoly (r : ℝ) : (L * f r - A) ^ 2 =
      L ^ 2 * (f r) ^ 2 - (2 * L * A) * f r + A ^ 2 := by ring
  have hint : (∫ r in a..b, (L * f r - A) ^ 2) =
      L ^ 2 * (∫ r in a..b, (f r) ^ 2) - L * A ^ 2 := by
    simp_rw [hpoly]
    rw [intervalIntegral.integral_add
        ((hi2.const_mul (L ^ 2)).sub (hi.const_mul (2 * L * A))) intervalIntegrable_const,
      intervalIntegral.integral_sub (hi2.const_mul (L ^ 2)) (hi.const_mul (2 * L * A)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    change L ^ 2 * (∫ r in a..b, (f r) ^ 2) - (2 * L * A) * A + L * A ^ 2 = _
    ring
  rw [hint] at hnonneg
  have hscaled : L * A ^ 2 ≤ L * (L * (∫ r in a..b, (f r) ^ 2)) := by
    nlinarith
  exact (mul_le_mul_left hL).mp hscaled

theorem intervalIntegral_norm_sq_le_length_mul_integral_norm_sq
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ‖∫ r in a..b, f r‖ ^ 2 ≤ (b - a) * (∫ r in a..b, ‖f r‖ ^ 2) := by
  calc
    _ ≤ (∫ r in a..b, ‖f r‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (intervalIntegral.norm_integral_le_integral_norm hab) 2
    _ ≤ _ := intervalIntegral_sq_le_length_mul_integral_sq hab hf.norm

theorem coefficient_norm_sq_le_energy (N : ℕ) (c : FourierCoeff)
    {k : Frequency} (hk : k ∈ cutoffModes N) (i : Fin 3) :
    ‖c k i‖ ^ 2 ≤ coefficientEnergy N c := by
  rw [← Complex.normSq_eq_norm_sq]
  calc
    _ ≤ ∑ j : Fin 3, Complex.normSq (c k j) :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ p ∈ cutoffModes N, ∑ j : Fin 3, Complex.normSq (c p j) :=
      Finset.single_le_sum
        (fun p _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)) hk

theorem GalerkinSolution.coefficient_integral_rhs
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {k : Frequency} (hk : k ∈ cutoffModes N) (i : Fin 3)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, galerkinRhs ν N (g.coeff r) k i) = g.coeff t k i - g.coeff s k i := by
  have hcont : ContinuousOn (fun r => g.coeff r k i) (Icc s t) :=
    (g.coefficient_continuous k i).mono (fun r hr => hs.trans hr.1)
  have hrhs : ContinuousOn (fun r => galerkinRhs ν N (g.coeff r) k i) (Icc s t) :=
    (g.rhs_continuousOn hk i).mono (fun r hr => hs.trans hr.1)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont
    _ (hrhs.intervalIntegrable_of_Icc hst)
  intro r hr
  have hrpos : 0 < r := hs.trans_lt hr.1
  exact (g.equation r hrpos.le k hk i).hasDerivAt (Ici_mem_nhds hrpos)

/-- The actual derivative integral controls every coefficient increment. -/
theorem GalerkinSolution.coefficient_time_modulus
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (i : Fin 3) {s t T : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖g.coeff t k i - g.coeff s k i‖ ^ 2 ≤
      (t - s) * (∫ r in (0 : ℝ)..T,
        ∫ x in unitCube, ‖timeDerivative g.velocity r x‖ ^ 2) := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hlen : 0 ≤ t - s := sub_nonneg.mpr hst
  by_cases hk : k ∈ cutoffModes N
  · have hrhs : ContinuousOn (fun r => galerkinRhs ν N (g.coeff r) k i) (Icc s t) :=
      (g.rhs_continuousOn hk i).mono (fun r hr => hs.trans hr.1)
    have hlocal := intervalIntegral_norm_sq_le_length_mul_integral_norm_sq hst hrhs
    rw [g.coefficient_integral_rhs hk i hs hst] at hlocal
    have henergy : ContinuousOn (fun r => ∫ x in unitCube,
        ‖timeDerivative g.velocity r x‖ ^ 2) (Icc s t) :=
      g.timeDerivative_energy_continuousOn.mono (fun r hr => hs.trans hr.1)
    have hcompare : (∫ r in s..t, ‖galerkinRhs ν N (g.coeff r) k i‖ ^ 2) ≤
        ∫ r in s..t, ∫ x in unitCube, ‖timeDerivative g.velocity r x‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hst
        ((hrhs.norm.pow 2).intervalIntegrable_of_Icc hst)
        (henergy.intervalIntegrable_of_Icc hst)
      intro r hr
      rw [g.timeDerivative_energy_eq r (hs.trans hr.1)]
      exact coefficient_norm_sq_le_energy N _ hk i
    have hfull : (∫ r in s..t, ∫ x in unitCube,
        ‖timeDerivative g.velocity r x‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..T, ∫ x in unitCube, ‖timeDerivative g.velocity r x‖ ^ 2 := by
      apply intervalIntegral.integral_mono_interval hs hst htT
      · exact Filter.Eventually.of_forall fun r => integral_nonneg (fun x => sq_nonneg _)
      · exact g.timeDerivative_energy_intervalIntegrable hT
    exact hlocal.trans (mul_le_mul_of_nonneg_left (hcompare.trans hfull) hlen)
  · rw [g.mode_support t (hs.trans hst) k hk i, g.mode_support s hs k hk i]
    simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    apply mul_nonneg hlen
    exact intervalIntegral.integral_nonneg_of_forall hT
      (fun r => integral_nonneg (fun x => sq_nonneg _))

/-- A single squared time modulus controls all cutoffs and all Fourier coordinates. -/
theorem AX6_UNIFORM_COEFFICIENT_TIME_MODULUS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ k : Frequency, ∀ i : Fin 3, ∀ s t : ℝ,
        0 ≤ s → s ≤ t → t ≤ T →
        ‖g.coeff t k i - g.coeff s k i‖ ^ 2 ≤ (t - s) * B := by
  obtain ⟨B, hB, hbound⟩ := AX6_UNIFORM_TIME_DERIVATIVE_BOUND hAX6 ν hν a ha T hT
  refine ⟨B, hB, ?_⟩
  intro N hN g k i s t hs hst htT
  exact (g.coefficient_time_modulus k i hs hst htT).trans
    (mul_le_mul_of_nonneg_left (hbound N hN g) (sub_nonneg.mpr hst))

end

end SingularClosure
