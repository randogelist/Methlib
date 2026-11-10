import NSE_NOH_FourierSpectral

/-!
# NSE_NOH FIX21: Fourier weak-test functional and exact spectral factorization

For a genuine complex L² class on the unit 3-torus, the integral of
(-2*pi*i*k₀) times the conjugate k-th Fourier monomial times the class
is exactly (-2*pi*i*k₀) times the k-th Fourier coefficient.

The multiplier is the classical coordinate derivative of the conjugate
Fourier monomial. This module proves the precise *integral/multiplier*
identity, the nonzero-frequency implication, and complex 2D3C
factorization. The independent calculus identity relating that multiplier
to the derivative of the real periodic test, the change of variables from
the cubical weak test to normalized Haar integration, and real-vector
complexification remain OPEN. In particular no claim is made that the
frozen `WeakX1Invariant` hypothesis is already connected to this test.

All results here are candidates for external native Windows Lean 4.33.0
compilation and theorem-level standard-only dependency inspection.
No local Lean execution.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory Filter
open scoped ENNReal Topology

namespace NSE_NOH
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! The multiplier associated to the derivative of the conjugate
complex Fourier monomial in the first spatial coordinate. -/
def firstFourierMultiplier (k : Fin 3 → ℤ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ))

/-! A genuine Bochner integral against the conjugate Fourier monomial.
This does not define the original real/cubical WeakX1Invariant predicate. -/
def firstFourierModeTest (a : ComplexL2Three) (k : Fin 3 → ℤ) : ℂ :=
  ∫ x : Torus 3,
    (firstFourierMultiplier k) •
      (UnitAddTorus.mFourier (-k) x • a x)

/-! Exact integral identity, not a synthetically imposed zero condition. -/
theorem firstFourierModeTest_eq_multiplier
    (a : ComplexL2Three) (k : Fin 3 → ℤ) :
    firstFourierModeTest a k =
      (firstFourierMultiplier k) • UnitAddTorus.mFourierCoeff a k := by
  simp only [firstFourierModeTest, UnitAddTorus.mFourierCoeff, integral_smul]

/-! All nonzero-first-index Fourier multipliers are nonzero. -/
theorem firstFourierMultiplier_ne_zero
    (k : Fin 3 → ℤ) (hk : k 0 ≠ 0) :
    firstFourierMultiplier k ≠ 0 := by
  have hkC : (k 0 : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold firstFourierMultiplier
  exact neg_ne_zero.mpr
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
      hkC)

/-! The genuine weak-test functional vanishes precisely when the complex
L² Fourier coefficient vanishes at every mode with k₀ ≠ 0. -/
theorem firstFourierModeTest_zero_iff_zeroFirst
    (a : ComplexL2Three) :
    (∀ k : Fin 3 → ℤ, firstFourierModeTest a k = 0) ↔
    (∀ k : Fin 3 → ℤ, k 0 ≠ 0 →
      UnitAddTorus.mFourierCoeff a k = 0) := by
  constructor
  · intro h k hk
    have hmul : firstFourierMultiplier k *
      UnitAddTorus.mFourierCoeff a k = 0 := by
      simpa only [smul_eq_mul] using
        ((firstFourierModeTest_eq_multiplier a k).symm.trans (h k))
    exact (mul_eq_zero.mp hmul).resolve_left
      (firstFourierMultiplier_ne_zero k hk)
  · intro h k
    rw [firstFourierModeTest_eq_multiplier]
    by_cases hk : k 0 = 0
    · simp [firstFourierMultiplier, hk]
    · simp only [h k hk, smul_zero]

/-! Main new exact spectral consequence: zero of the actual integral
Fourier-mode tests implies planar complex L² factorization. -/
theorem complexL2_firstFourierModeTest_factorization
    (a : ComplexL2Three)
    (h : ∀ k : Fin 3 → ℤ, firstFourierModeTest a k = 0) :
    ∃ w : ComplexL2Two, complexL2Pullback w = a := by
  exact complexL2_zeroFirstSpectral_factorization a
    ((firstFourierModeTest_zero_iff_zeroFirst a).mp h)

/-! Componentwise complex analogue of the 2D3C trace factorization.
The real-valued 3D L² vector representation remains a distinct task. -/
def ThreeComponentFirstFourierModeTestZero
    (a : Fin 3 → ComplexL2Three) : Prop :=
  ∀ i : Fin 3, ∀ k : Fin 3 → ℤ, firstFourierModeTest (a i) k = 0

theorem complexL2_threeComponentFirstFourierModeTest_factorization
    (a : Fin 3 → ComplexL2Three)
    (h : ThreeComponentFirstFourierModeTestZero a) :
    ∃ w : ComplexL2Two, ∃ v : Fin 2 → ComplexL2Two,
      complexL2Pullback w = a 0 ∧
      (∀ i : Fin 2, complexL2Pullback (v i) = a (Fin.succ i)) := by
  classical
  obtain ⟨w, hw⟩ :=
    complexL2_firstFourierModeTest_factorization (a 0) (h 0)
  have hvExists : ∀ i : Fin 2, ∃ z : ComplexL2Two,
      complexL2Pullback z = a (Fin.succ i) := by
    intro i
    exact complexL2_firstFourierModeTest_factorization
      (a (Fin.succ i)) (h (Fin.succ i))
  choose v hv using hvExists
  exact ⟨w, v, hw, hv⟩

end
end NSE_NOH

#check NSE_NOH.firstFourierMultiplier
#check NSE_NOH.firstFourierModeTest
#print axioms NSE_NOH.firstFourierModeTest_eq_multiplier
#print axioms NSE_NOH.firstFourierMultiplier_ne_zero
#print axioms NSE_NOH.firstFourierModeTest_zero_iff_zeroFirst
#print axioms NSE_NOH.complexL2_firstFourierModeTest_factorization
#check NSE_NOH.ThreeComponentFirstFourierModeTestZero
#print axioms NSE_NOH.complexL2_threeComponentFirstFourierModeTest_factorization
