import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic
import PrimeSpectralSeries

/-!
Finite-rank diagonal operators on the actual real Hilbert sum `lp ... 2`.
For sigma > 1 the prime vector is constructed using the series summability
edge in `PrimeSpectralSeries`.  This module does not claim an unbounded energy
operator, functional calculus, semigroup, or resolvent identity.
-/

noncomputable section
open scoped BigOperators
open Filter
open scoped Topology

namespace PrimeSpectralHilbert

abbrev PrimeHilbert := lp (fun _ : ℕ => ℝ) 2

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual prime amplitudes are square summable for sigma > 1. -/
theorem primeAmplitude_memlp (sigma : ℝ) (hsigma : 1 < sigma) :
    Memℓp (PrimeSpectralTheta.amplitude sigma) 2 := by
  apply memℓp_gen
  have h := PrimeSpectralSeries.vector_sq_summable sigma hsigma
  simpa [PrimeSpectralSeries.vector, Real.norm_eq_abs, Real.rpow_two, sq_abs] using h

/-- The proposed actual prime vector as an element of real `lp`-two space. -/
def actualPrimeVector (sigma : ℝ) (hsigma : 1 < sigma) : PrimeHilbert :=
  ⟨PrimeSpectralTheta.amplitude sigma, primeAmplitude_memlp sigma hsigma⟩

theorem actualPrimeVector_apply (sigma : ℝ) (hsigma : 1 < sigma) (n : ℕ) :
    actualPrimeVector sigma hsigma n = PrimeSpectralTheta.amplitude sigma n := by
  rfl

/-- An actual Hilbert vector from the stated square-summability input. -/
def primeVector (sigma : ℝ)
    (hsq : Summable (fun n : ℕ =>
      ‖PrimeSpectralTheta.amplitude sigma n‖ ^ (2 : ℝ≥0∞).toReal)) :
    PrimeHilbert :=
  ⟨PrimeSpectralTheta.amplitude sigma, memℓp_gen hsq⟩

theorem primeVector_apply (sigma : ℝ)
    (hsq : Summable (fun n : ℕ =>
      ‖PrimeSpectralTheta.amplitude sigma n‖ ^ (2 : ℝ≥0∞).toReal))
    (n : ℕ) : primeVector sigma hsq n = PrimeSpectralTheta.amplitude sigma n := by
  rfl

/-- Evaluation followed by reinsertion at a single coordinate is bounded. -/
def coordinate (n : ℕ) : PrimeHilbert →L[ℝ] PrimeHilbert :=
  (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 n).comp
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)

theorem coordinate_apply (n : ℕ) (v : PrimeHilbert) :
    coordinate n v = lp.single 2 n (v n) := by
  rfl

/-- Finite-support diagonal multiplication, as a bounded operator on `lp`. -/
def finiteDiagonal (s : Finset ℕ) (weight : ℕ → ℝ) :
    PrimeHilbert →L[ℝ] PrimeHilbert :=
  ∑ n ∈ s, weight n • coordinate n

/-- Its actual Hilbert matrix element is the finite diagonal sum. -/
theorem finiteDiagonal_matrix_element (s : Finset ℕ) (weight : ℕ → ℝ)
    (v : PrimeHilbert) :
    inner ℝ v (finiteDiagonal s weight v) =
      ∑ n ∈ s, v n * (weight n * v n) := by
  classical
  simp [finiteDiagonal, coordinate_apply, inner_sum,
    lp.inner_single_right, Real.inner_apply, mul_comm, mul_left_comm, mul_assoc]

/-- The exact theta cutoff, conditional only on the exhibited amplitudes being
the coordinates of an actual `lp` vector. -/
theorem theta_matrix_element_of_coordinates (sigma x : ℝ) (v : PrimeHilbert)
    (hv : ∀ n : ℕ, v n = PrimeSpectralTheta.amplitude sigma n) :
    inner ℝ v
        (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) v) = Chebyshev.theta x := by
  rw [finiteDiagonal_matrix_element]
  calc
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
      v n * (PrimeSpectralTheta.unweight sigma n * v n)) =
        PrimeSpectralTheta.cutoffPairing sigma x := by
          unfold PrimeSpectralTheta.cutoffPairing
          apply Finset.sum_congr rfl
          intro n hn
          rw [hv n]
    _ = Chebyshev.theta x :=
      PrimeSpectralTheta.cutoffPairing_eq_chebyshev_theta sigma x

/-- A concrete Hilbert-vector theta identity once its square-summability is
supplied.  No analytic continuation or PNT premise appears. -/
theorem theta_matrix_element_of_square_summability (sigma x : ℝ)
    (hsq : Summable (fun n : ℕ =>
      ‖PrimeSpectralTheta.amplitude sigma n‖ ^ (2 : ℝ≥0∞).toReal)) :
    inner ℝ (primeVector sigma hsq)
      (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
        (PrimeSpectralTheta.unweight sigma) (primeVector sigma hsq)) =
          Chebyshev.theta x := by
  apply theta_matrix_element_of_coordinates
  intro n
  exact primeVector_apply sigma hsq n

/-- The actual theta cutoff as a bounded operator on the actual Hilbert
prime vector, for each sigma > 1 and each real cutoff x. -/
theorem theta_matrix_element (sigma x : ℝ) (hsigma : 1 < sigma) :
    inner ℝ (actualPrimeVector sigma hsigma)
      (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
        (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) =
          Chebyshev.theta x := by
  apply theta_matrix_element_of_coordinates
  intro n
  exact actualPrimeVector_apply sigma hsigma n

/-- Every finite heat truncation is a matrix element of a bounded operator. -/
theorem finite_heat_matrix_element (sigma t : ℝ) (hsigma : 1 < sigma) (N : ℕ) :
    inner ℝ (actualPrimeVector sigma hsigma)
      (finiteDiagonal (Finset.range N)
        (fun n => Real.exp (-t * Real.log (n : ℝ)))
        (actualPrimeVector sigma hsigma)) =
      ∑ n ∈ Finset.range N, PrimeSpectralSeries.heatTerm sigma t n := by
  rw [finiteDiagonal_matrix_element]
  apply Finset.sum_congr rfl
  intro n hn
  rw [actualPrimeVector_apply]
  unfold PrimeSpectralSeries.heatTerm PrimeSpectralSeries.vector
  ring

/-- The finite-rank heat matrix elements converge to the actual zeta
logarithmic derivative.  This uses the existing Mathlib zeta-series bridge;
it is not an independent derivation of that bridge. -/
theorem finite_heat_matrix_elements_tendsto_zeta (sigma t : ℝ)
    (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ =>
      (inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal (Finset.range N)
          (fun n => Real.exp (-t * Real.log (n : ℝ)))
          (actualPrimeVector sigma hsigma)) : ℂ)) atTop
      (𝓝 (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ)))) := by
  simpa only [finite_heat_matrix_element, Complex.ofReal_sum] using
    (PrimeSpectralSeries.heat_hasSum_actual_zeta sigma t hsigma ht).tendsto_sum_nat

end PrimeSpectralHilbert
