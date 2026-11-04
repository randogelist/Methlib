import HVRFrequencyCellBudget

/-!
Actual frequency weights for the finite-cell approximation. This is a
standalone candidate: it discharges the integrability and L1 mass needed to
apply HVRFrequencyCellBudget to the weight `ψ(t) exp(i t x)`. It does not
construct frequency cells, prove quadrature convergence, or establish the
continuous-frequency Fubini identity. No Lean was executed locally.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace HVRFrequencyWeightedCoefficients

/-- Actual weight whose cell integrals are quadrature coefficients. -/
def weightedFrequency (ψ : ℝ → ℂ) (x t : ℝ) : ℂ :=
  ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))

/-- The spatial phase has modulus one. -/
theorem norm_weightedFrequency (ψ : ℝ → ℂ) (x t : ℝ) :
    ‖weightedFrequency ψ x t‖ = ‖ψ t‖ := by
  have hexp : ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  simp only [weightedFrequency, norm_mul, hexp, mul_one]

/-- An integrable frequency test gives an integrable actual weight. -/
theorem weightedFrequency_integrable {μ : Measure ℝ}
    (ψ : ℝ → ℂ) (x : ℝ) (hψ : Integrable ψ μ) :
    Integrable (weightedFrequency ψ x) μ := by
  have hexp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (weightedFrequency ψ x) μ := by
    unfold weightedFrequency
    exact hψ.aestronglyMeasurable.mul hexp.measurable.aestronglyMeasurable
  apply Integrable.mono' hψ.norm hmeas
  filter_upwards [] with t
  simp only [norm_weightedFrequency, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), le_refl]

/-- The actual quadrature coefficients inherit the frequency test's L1
budget for any finite pairwise-disjoint measurable family of cells. -/
theorem actual_coefficients_norm_sum_le
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (ψ : ℝ → ℂ) (x : ℝ)
    (hψ : Integrable ψ μ)
    (hcell : ∀ i ∈ S, MeasurableSet (cell i))
    (hdisj : Set.Pairwise (↑S : Set ι) (fun i j => Disjoint (cell i) (cell j))) :
    (∑ i ∈ S, ‖∫ t : ℝ in cell i, weightedFrequency ψ x t ∂μ‖) ≤
      ∫ t : ℝ, ‖ψ t‖ ∂μ := by
  have h := HVRFrequencyCellBudget.disjoint_cells_coefficient_norm_sum_le
    S cell (weightedFrequency ψ x) (weightedFrequency_integrable ψ x hψ) hcell hdisj
  simpa only [norm_weightedFrequency] using h

end HVRFrequencyWeightedCoefficients
