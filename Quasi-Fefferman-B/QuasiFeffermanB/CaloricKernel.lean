import Mathlib

/-! Exact scalar heat-kernel integrals for the unit-torus caloric estimates. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace QuasiFeffermanB
noncomputable section

/-- A single differentiated heat mode has squared temporal L2 norm 1/(2ν),
independently of its nonzero frequency. -/
theorem HEAT_MULTIPLIER_SQUARE_INTEGRAL
    (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    (∫ t : ℝ in Ioi 0, (κ * Real.exp (-ν * κ ^ 2 * t)) ^ 2) = 1 / (2 * ν) := by
  have hdecay : -2 * ν * κ ^ 2 < 0 := by
    nlinarith [mul_pos hν (sq_pos_of_pos hκ)]
  have hfun :
      (fun t : ℝ => (κ * Real.exp (-ν * κ ^ 2 * t)) ^ 2) =
      (fun t : ℝ => κ ^ 2 * Real.exp ((-2 * ν * κ ^ 2) * t)) := by
    funext t
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    congr 2 <;> ring
  rw [hfun, integral_const_mul, integral_exp_mul_Ioi hdecay]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_gt hν, ne_of_gt hκ]
  <;> ring

/-- Exact pairwise heat integral appearing in the finite caloric quadratic
form. No Fourier lattice estimate is used. -/
theorem HEAT_PAIR_INTEGRAL
    (ν κ η : ℝ) (hν : 0 < ν) (hfreq : 0 < κ ^ 2 + η ^ 2) :
    (∫ t : ℝ in Ioi 0,
      Real.exp (-ν * κ ^ 2 * t) * Real.exp (-ν * η ^ 2 * t)) =
      1 / (ν * (κ ^ 2 + η ^ 2)) := by
  have hdecay : -(ν * (κ ^ 2 + η ^ 2)) < 0 := neg_lt_zero.mpr (mul_pos hν hfreq)
  have hfun :
      (fun t : ℝ => Real.exp (-ν * κ ^ 2 * t) * Real.exp (-ν * η ^ 2 * t)) =
      (fun t : ℝ => Real.exp ((-(ν * (κ ^ 2 + η ^ 2))) * t)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, integral_exp_mul_Ioi hdecay]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

/-- The preceding pairwise heat integrand is integrable. -/
theorem HEAT_PAIR_INTEGRABLE
    (ν κ η : ℝ) (hν : 0 < ν) (hfreq : 0 < κ ^ 2 + η ^ 2) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-ν * κ ^ 2 * t) * Real.exp (-ν * η ^ 2 * t)) (Ioi 0) := by
  have hdecay : -(ν * (κ ^ 2 + η ^ 2)) < 0 := neg_lt_zero.mpr (mul_pos hν hfreq)
  convert integrableOn_exp_mul_Ioi hdecay 0 using 1
  funext t
  rw [← Real.exp_add]
  congr 1
  ring

/-- Finite scalar heat-orbit ℓ¹ expression; Euclidean Fourier coefficient
magnitudes are the intended nonnegative weights. -/
def finiteHeatSum {ι : Type*} (s : Finset ι) (κ a : ι → ℝ) (ν t : ℝ) : ℝ :=
  ∑ i ∈ s, a i * Real.exp (-ν * κ i ^ 2 * t)

/-- Finite caloric quadratic form before taking an infinite Fourier limit. -/
def finiteCaloricQuadratic {ι : Type*} (s : Finset ι) (κ a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, (a i * a j) / (κ i ^ 2 + κ j ^ 2)

/-- Squared finite heat sums are integrable on the full positive time axis. -/
theorem FINITE_HEAT_SQUARE_INTEGRABLE
    {ι : Type*} (s : Finset ι) (κ a : ι → ℝ) (ν : ℝ) (hν : 0 < ν)
    (hκ : ∀ i ∈ s, 0 < κ i) :
    IntegrableOn (fun t : ℝ => finiteHeatSum s κ a ν t ^ 2) (Ioi 0) := by
  have hF : ∀ i ∈ s, ∀ j ∈ s, IntegrableOn (fun t : ℝ =>
      (a i * a j) * (Real.exp (-ν * κ i ^ 2 * t) * Real.exp (-ν * κ j ^ 2 * t)))
      (Ioi 0) := by
    intro i hi j hj
    exact (HEAT_PAIR_INTEGRABLE ν (κ i) (κ j) hν
      (add_pos (sq_pos_of_pos (hκ i hi)) (sq_pos_of_pos (hκ j hj)))).const_mul _
  convert integrable_finsetSum s (fun i hi =>
    integrable_finsetSum s (fun j hj => hF i hi j hj)) using 1
  funext t
  unfold finiteHeatSum
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact finite heat-orbit identity, with finite-sum integration justified
by pairwise exponential integrability. -/
theorem FINITE_HEAT_SQUARE_INTEGRAL
    {ι : Type*} (s : Finset ι) (κ a : ι → ℝ) (ν : ℝ) (hν : 0 < ν)
    (hκ : ∀ i ∈ s, 0 < κ i) :
    (∫ t : ℝ in Ioi 0, finiteHeatSum s κ a ν t ^ 2) =
      finiteCaloricQuadratic s κ a / ν := by
  have hfreq : ∀ i ∈ s, ∀ j ∈ s, 0 < κ i ^ 2 + κ j ^ 2 := by
    intro i hi j hj
    exact add_pos (sq_pos_of_pos (hκ i hi)) (sq_pos_of_pos (hκ j hj))
  let F : ι → ι → ℝ → ℝ := fun i j t =>
    (a i * a j) * (Real.exp (-ν * κ i ^ 2 * t) * Real.exp (-ν * κ j ^ 2 * t))
  have hF : ∀ i ∈ s, ∀ j ∈ s, IntegrableOn (F i j) (Ioi 0) := by
    intro i hi j hj
    exact (HEAT_PAIR_INTEGRABLE ν (κ i) (κ j) hν (hfreq i hi j hj)).const_mul
      (a i * a j)
  have hsum : (fun t : ℝ => finiteHeatSum s κ a ν t ^ 2) =
      (fun t : ℝ => ∑ i ∈ s, ∑ j ∈ s, F i j t) := by
    funext t
    unfold finiteHeatSum
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [F]
    ring
  calc
    (∫ t : ℝ in Ioi 0, finiteHeatSum s κ a ν t ^ 2) =
        ∑ i ∈ s, ∑ j ∈ s, (a i * a j) / (ν * (κ i ^ 2 + κ j ^ 2)) := by
      rw [hsum, integral_finsetSum s
        (fun i hi => integrable_finsetSum s (fun j hj => hF i hi j hj))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum s (fun j hj => hF i hi j hj)]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [F]
      rw [integral_const_mul, HEAT_PAIR_INTEGRAL ν (κ i) (κ j) hν (hfreq i hi j hj)]
      ring
    _ = finiteCaloricQuadratic s κ a / ν := by
      unfold finiteCaloricQuadratic
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [ne_of_gt hν, ne_of_gt (hfreq i hi j hj)]
      <;> ring

end
end QuasiFeffermanB
