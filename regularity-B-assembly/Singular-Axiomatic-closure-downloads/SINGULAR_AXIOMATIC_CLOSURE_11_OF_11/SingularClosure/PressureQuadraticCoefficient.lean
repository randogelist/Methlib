import SingularClosure.InfiniteFourierPressure

/-! The exact quadratic Fourier formula for the actual infinite pressure.
The tensor indices are explicitly transposed in the finite coordinate sums;
the frequency convolution remains the genuinely convergent infinite sum. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

def pressureQuadraticNumerator (c : TorusSobolev 0) (k : Frequency) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
    (∑' p : Frequency, c.val p i * c.val (k - p) j)

theorem fullTransport_pressure_pairing (c : TorusSobolev 0) (k : Frequency) :
    (∑ i : Fin 3, (k i : ℂ) * fullTransportCoefficients c k i) =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * pressureQuadraticNumerator c k := by
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) *
        (derivativeSymbol j k * (∑' p : Frequency, c.val p j * c.val (k - p) i)) := by
      simp only [fullTransportCoefficients, divergenceTransportCoefficient_apply, Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, (k j : ℂ) *
        (derivativeSymbol i k * (∑' p : Frequency, c.val p i * c.val (k - p) j)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      unfold pressureQuadraticNumerator
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
      ring

/-- The nonzero pressure mode has exactly the frozen quadratic numerator and
the unscaled integer-frequency denominator. -/
theorem infinitePressureCoefficient_fullTransport_nonzero
    (c : TorusSobolev 0) (k : Frequency) (hk : k ≠ 0) :
    infinitePressureCoefficient (fullTransportCoefficients c) k =
      -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
          (∑' p : Frequency, c.val p i * c.val (k - p) j)) /
        (∑ i : Fin 3, (k i : ℂ) ^ 2) := by
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  have hden := frequency_complex_square_sum_ne_zero k hk
  have hI : Complex.I *
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I * pressureQuadraticNumerator c k) =
        ((2 * Real.pi : ℝ) : ℂ) * (-pressureQuadraticNumerator c k) := by
    calc
      _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ 2 * pressureQuadraticNumerator c k := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  change infinitePressureCoefficient (fullTransportCoefficients c) k =
    -pressureQuadraticNumerator c k / (∑ i : Fin 3, (k i : ℂ) ^ 2)
  simp only [infinitePressureCoefficient, pressureFromTransport, if_neg hk]
  rw [fullTransport_pressure_pairing, hI]
  field_simp [hpi, hden] <;> ring

theorem infinitePressureCoefficient_fullTransport_quadratic
    (c : TorusSobolev 0) (k : Frequency) :
    infinitePressureCoefficient (fullTransportCoefficients c) k =
      if k = 0 then 0 else
        -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
            (∑' p : Frequency, c.val p i * c.val (k - p) j)) /
          (∑ i : Fin 3, (k i : ℂ) ^ 2) := by
  by_cases hk : k = 0
  · subst k
    simp only [infinitePressureCoefficient_zero, ite_true]
  · rw [if_neg hk]
    exact infinitePressureCoefficient_fullTransport_nonzero c k hk

/-- The displayed formula is the actual cube Fourier integral of the actual
smooth pressure, with no separate coefficient-identification premise. -/
theorem fullTransportPressure_fourierCoeff_quadratic
    (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) (k : Frequency) :
    (∫ x in unitCube, star (fourierCharacter k x) * (fullTransportPressure c x : ℂ)) =
      if k = 0 then 0 else
        -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
            (∑' p : Frequency, c.val p i * c.val (k - p) j)) /
          (∑ i : Fin 3, (k i : ℂ) ^ 2) := by
  change (∫ x in unitCube, star (fourierCharacter k x) *
    (infiniteTransportPressure (fullTransportCoefficients c) x : ℂ)) = _
  rw [infiniteTransportPressure_coeff _
    (divergenceTransport_rapid c hc hreal hsol)
    (divergenceTransport_reality c hc hreal hsol)]
  exact infinitePressureCoefficient_fullTransport_quadratic c k

theorem fullTransportPressure_fourierCoeff_zero
    (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    (∫ x in unitCube, star (fourierCharacter 0 x) * (fullTransportPressure c x : ℂ)) = 0 := by
  simpa only [ite_true] using fullTransportPressure_fourierCoeff_quadratic c hc hreal hsol 0

theorem fullTransportPressure_fourierCoeff_nonzero
    (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val)
    (k : Frequency) (hk : k ≠ 0) :
    (∫ x in unitCube, star (fourierCharacter k x) * (fullTransportPressure c x : ℂ)) =
      -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
          (∑' p : Frequency, c.val p i * c.val (k - p) j)) /
        (∑ i : Fin 3, (k i : ℂ) ^ 2) := by
  simpa only [if_neg hk] using fullTransportPressure_fourierCoeff_quadratic c hc hreal hsol k

end

end SingularClosure
