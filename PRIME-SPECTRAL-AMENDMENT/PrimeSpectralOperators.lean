import Mathlib.Analysis.Normed.Lp.lpHolder
import PrimeSpectralHilbert
import PrimeSpectralBridge

/-!
Actual bounded diagonal operators on the prime Hilbert space.

The heat operator has multipliers exp(-t log n), and the diagonal resolvent
candidate has multipliers (w + log n)⁻¹. Their ℓ² matrix elements are the
heat and resolvent series constructed in the independent modules. The scalar
zeta identification reuses Mathlib's pre-existing logarithmic-derivative
identity. No unbounded self-adjoint generator or its functional calculus is
constructed in this file.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace PrimeSpectralOperators
open PrimeSpectralHilbert

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

/-- Coordinatewise multiplication by a uniformly bounded real sequence. -/
def diagonal (m : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ n, |m n| ≤ K) : PrimeHilbert →L[ℝ] PrimeHilbert :=
  lp.mapCLM 2 (fun n : ℕ => m n • ContinuousLinearMap.id ℝ ℝ) hK (by
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hm n) (abs_nonneg x))

theorem diagonal_apply (m : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ n, |m n| ≤ K) (v : PrimeHilbert) (n : ℕ) :
    diagonal m K hK hm v n = m n * v n := by
  rfl

theorem diagonal_matrix_element (m : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ n, |m n| ≤ K) (v : PrimeHilbert) :
    inner ℝ v (diagonal m K hK hm v) =
      ∑' n : ℕ, v n * (m n * v n) := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [diagonal_apply]
  rw [Real.inner_apply]

def heatMultiplier (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * Real.log (n : ℝ))

theorem heatMultiplier_bound (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |heatMultiplier t n| ≤ 1 := by
  rw [heatMultiplier, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  nlinarith

/-- The positive-time heat multiplier as a bounded operator on the actual lp. -/
def heatOperator (t : ℝ) (ht : 0 ≤ t) : PrimeHilbert →L[ℝ] PrimeHilbert :=
  diagonal (heatMultiplier t) 1 (by norm_num) (heatMultiplier_bound t ht)

theorem heatOperator_apply (t : ℝ) (ht : 0 ≤ t) (v : PrimeHilbert) (n : ℕ) :
    heatOperator t ht v n = heatMultiplier t n * v n := by
  rfl

/-- The bounded heat multipliers compose according to addition of time. -/
theorem heatOperator_add (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    heatOperator (t + s) (add_nonneg ht hs) =
      (heatOperator t ht).comp (heatOperator s hs) := by
  ext v n
  simp only [ContinuousLinearMap.comp_apply, heatOperator_apply, heatMultiplier]
  have hexp : Real.exp (-(t + s) * Real.log (n : ℝ)) =
      Real.exp (-t * Real.log (n : ℝ)) * Real.exp (-s * Real.log (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem heat_matrix_element (sigma t : ℝ) (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    inner ℝ (actualPrimeVector sigma hsigma)
      (heatOperator t ht (actualPrimeVector sigma hsigma)) =
        ∑' n : ℕ, PrimeSpectralSeries.heatTerm sigma t n := by
  unfold heatOperator
  rw [diagonal_matrix_element]
  apply tsum_congr
  intro n
  simp only [actualPrimeVector_apply]
  unfold heatMultiplier PrimeSpectralSeries.heatTerm PrimeSpectralSeries.vector
  ring

/-- The actual bounded heat matrix element equals the actual zeta logarithmic
derivative, using the pre-existing Mathlib zeta-series identity. -/
theorem heat_matrix_element_actual_zeta (sigma t : ℝ)
    (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    (inner ℝ (actualPrimeVector sigma hsigma)
      (heatOperator t ht (actualPrimeVector sigma hsigma)) : ℂ) =
      -deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ)) := by
  rw [heat_matrix_element, Complex.ofReal_tsum]
  exact (PrimeSpectralSeries.heat_hasSum_actual_zeta sigma t hsigma ht).tsum_eq

def resolventMultiplier (w : ℝ) (n : ℕ) : ℝ :=
  (w + Real.log (n : ℝ))⁻¹

theorem resolventMultiplier_bound (w : ℝ) (hw : 0 < w) (n : ℕ) :
    |resolventMultiplier w n| ≤ w⁻¹ := by
  have hn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hpos : 0 < w + Real.log (n : ℝ) := by linarith
  rw [resolventMultiplier, abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_le_inv₀ hpos hw).2 (le_add_of_nonneg_right hn)

/-- Diagonal resolvent multiplier as a bounded operator on the actual lp. -/
def diagonalResolvent (w : ℝ) (hw : 0 < w) :
    PrimeHilbert →L[ℝ] PrimeHilbert :=
  diagonal (resolventMultiplier w) w⁻¹ (le_of_lt (inv_pos.mpr hw))
    (resolventMultiplier_bound w hw)

theorem diagonalResolvent_apply (w : ℝ) (hw : 0 < w)
    (v : PrimeHilbert) (n : ℕ) :
    diagonalResolvent w hw v n = (w + Real.log (n : ℝ))⁻¹ * v n := by
  rfl

/-- The bounded diagonal resolvents satisfy the resolvent identity. -/
theorem diagonalResolvent_identity (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    diagonalResolvent a ha - diagonalResolvent b hb =
      (b - a) • ((diagonalResolvent a ha).comp (diagonalResolvent b hb)) := by
  ext v n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, diagonalResolvent_apply, smul_eq_mul]
  have hn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hna : a + Real.log (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hnb : b + Real.log (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp [hna, hnb]
  <;> ring

/-- The diagonal resolvent has the expected spectral matrix element. -/
theorem resolvent_matrix_element (sigma w : ℝ) (hsigma : 1 < sigma) (hw : 0 < w) :
    inner ℝ (actualPrimeVector sigma hsigma)
      (diagonalResolvent w hw (actualPrimeVector sigma hsigma)) =
        ∑' n : ℕ, PrimeSpectralSeries.weight sigma n / (w + Real.log (n : ℝ)) := by
  unfold diagonalResolvent
  rw [diagonal_matrix_element]
  apply tsum_congr
  intro n
  simp only [actualPrimeVector_apply]
  unfold resolventMultiplier
  have hv : (PrimeSpectralTheta.amplitude sigma n) ^ 2 =
      PrimeSpectralSeries.weight sigma n := by
    simpa [PrimeSpectralSeries.vector] using PrimeSpectralSeries.vector_sq sigma n
  rw [div_eq_mul_inv, ← hv]
  ring

/-- The actual zeta Laplace integral equals the bounded diagonal resolvent
matrix element. The actual-zeta bridge remains explicitly reused. -/
theorem zeta_laplace_eq_resolvent_matrix_element (sigma w : ℝ)
    (hsigma : 1 < sigma) (hw : 0 < w) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-w * t) *
      (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ))).re) =
      inner ℝ (actualPrimeVector sigma hsigma)
        (diagonalResolvent w hw (actualPrimeVector sigma hsigma)) := by
  rw [resolvent_matrix_element]
  exact PrimeSpectralBridge.zeta_realpart_resolvent_laplace sigma w hsigma hw

end PrimeSpectralOperators
