import HVRPrimeLeftQuadrature

/-! One-variable integrability candidates for the finite-grid left limit.
These statements require an external Lean build, axiom audit and swap trace.
The separate equality of the interval and full kernels remains open. -/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRZetaHyperbolicFrequencyBounds
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open HVRPrimeLeftQuadrature
open scoped BigOperators Topology

namespace HVRPrimeLeftIntegrable

/-- Every finite sampled approximation is integrable without extra cell
integrability assumptions. -/
theorem sample_outer_integrable (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a : ℝ)
    (ha : 0 < a) : IntegrableOn
      (fun u : ℝ => dampedError a u * sampleKernel R N ψ x u) (Set.Ioi 0) := by
  have hsum : IntegrableOn (fun u : ℝ => ∑ i ∈ Finset.range N,
      (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t) *
        (dampedError a u * phase (gridPoint R N i) u)) (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro i hi
    exact (HVRPrimeDirectFrequency.damped_phase_integrable_direct
      a (gridPoint R N i) ha).const_mul _
  have heq : (fun u : ℝ => dampedError a u * sampleKernel R N ψ x u) =
      (fun u : ℝ => ∑ i ∈ Finset.range N,
        (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t) *
          (dampedError a u * phase (gridPoint R N i) u)) := by
    funext u
    unfold sampleKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const]
    ring
  rw [heq]
  exact hsum

/-- The two arguments of the Fourier phase are interchangeable. -/
theorem phase_symm (t u : ℝ) : phase t u = phase u t := by
  unfold phase
  congr 2
  push_cast
  ring

/-- The interval kernel is uniformly bounded by the test's L1 mass. -/
theorem intervalKernel_norm_le (R : ℝ) (ψ : ℝ → ℂ) (x u : ℝ)
    (hψ : Integrable ψ) : ‖intervalKernel R ψ x u‖ ≤ ∫ t : ℝ, ‖ψ t‖ := by
  let φ := weightedFrequency ψ x
  have hφ : Integrable φ := weightedFrequency_integrable ψ x hψ
  have hφcell : IntegrableOn (fun t : ℝ => ‖φ t‖) (Set.Ioc (-R) R) :=
    hφ.norm.mono_measure Measure.restrict_le_self
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-R) R),
      ‖φ t * phase t u‖ ≤ ‖φ t‖ := by
    filter_upwards [] with t
    have hp : ‖phase t u‖ = 1 := by
      simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    simp only [norm_mul, hp, mul_one, le_refl]
  have hnorm := norm_integral_le_of_norm_le hφcell hbound
  have hmass : (∫ t : ℝ in Set.Ioc (-R) R, ‖φ t‖) ≤ ∫ t : ℝ, ‖φ t‖ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun t => norm_nonneg (φ t))) hφ.norm
  exact le_trans (by simpa only [intervalKernel, φ] using hnorm)
    (by simpa only [φ, norm_weightedFrequency] using hmass)

/-- Compact frequency support provides the first frequency moment. -/
theorem weighted_frequency_moment_integrable (R : ℝ) (ψ : ℝ → ℂ) (x : ℝ)
    (hR : 0 ≤ R) (hψ : Integrable ψ) : IntegrableOn
      (fun t : ℝ => |t| * ‖weightedFrequency ψ x t‖) (Set.Ioc (-R) R) := by
  let φ := weightedFrequency ψ x
  have hφ : Integrable φ := weightedFrequency_integrable ψ x hψ
  have hcell : IntegrableOn φ (Set.Ioc (-R) R) :=
    hφ.mono_measure Measure.restrict_le_self
  have hmajor : IntegrableOn (fun t : ℝ => R * ‖φ t‖) (Set.Ioc (-R) R) :=
    hcell.norm.const_mul R
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |t| * ‖φ t‖)
      (volume.restrict (Set.Ioc (-R) R)) :=
    (continuous_id.abs.measurable.aestronglyMeasurable).mul
      hcell.aestronglyMeasurable.norm
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htR : |t| ≤ R := abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right htR (norm_nonneg _)

/-- The bounded-interval frequency integral is continuous in its phase. -/
theorem intervalKernel_continuous (R : ℝ) (ψ : ℝ → ℂ) (x : ℝ)
    (hR : 0 ≤ R) (hψ : Integrable ψ) :
    Continuous (intervalKernel R ψ x) := by
  let φ := weightedFrequency ψ x
  let μ := volume.restrict (Set.Ioc (-R) R)
  let M : ℝ := ∫ t : ℝ in Set.Ioc (-R) R, |t| * ‖φ t‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun t => mul_nonneg (abs_nonneg t) (norm_nonneg _))
  have hφ : Integrable φ μ :=
    (weightedFrequency_integrable ψ x hψ).mono_measure Measure.restrict_le_self
  have hw : Integrable (fun t : ℝ => |t| * ‖φ t‖) μ :=
    weighted_frequency_moment_integrable R ψ x hR hψ
  have hfreq : ∀ u : ℝ, Integrable (fun t : ℝ => φ t * phase u t) μ := by
    intro u
    have h := phase_mul_integrable φ u hφ
    simpa only [phase_symm] using h
  let K : NNReal := ⟨M, hM⟩
  have hL : LipschitzWith K (intervalKernel R ψ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (intervalKernel R ψ x u) (intervalKernel R ψ x v) ≤ M * dist u v
    have h := integral_phase_frequency_lipschitz φ u v (hfreq u) (hfreq v) hw
    simpa only [intervalKernel, φ, μ, M, phase_symm, dist_eq_norm,
      Real.norm_eq_abs, mul_comm] using h
  exact hL.continuous

/-- The actual interval-kernel outer integrand is controlled by the damped
prime-density L1 majorant. -/
theorem interval_outer_integrable (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ) : IntegrableOn
      (fun u : ℝ => dampedError a u * intervalKernel R ψ x u) (Set.Ioi 0) := by
  let B : ℝ := ∫ t : ℝ, ‖ψ t‖
  have hdamped := HVRPrimeDirectFrequency.dampedError_integrable_direct a ha
  have hmajor : IntegrableOn (fun u : ℝ => B * ‖dampedError a u‖) (Set.Ioi 0) :=
    hdamped.norm.const_mul B
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => dampedError a u * intervalKernel R ψ x u)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hdamped.aestronglyMeasurable.mul
      (intervalKernel_continuous R ψ x hR hψ).measurable.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [] with u
  calc
    ‖dampedError a u * intervalKernel R ψ x u‖ =
        ‖dampedError a u‖ * ‖intervalKernel R ψ x u‖ := norm_mul _ _
    _ ≤ ‖dampedError a u‖ * B :=
      mul_le_mul_of_nonneg_left (intervalKernel_norm_le R ψ x u hψ) (norm_nonneg _)
    _ = B * ‖dampedError a u‖ := mul_comm _ _

/-- The actual left finite-grid integrals converge to the interval-kernel
integral using only the direct L1 estimates and first moment. -/
theorem left_integrals_tendsto_direct (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ) :
    Tendsto (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError a u * sampleKernel R N ψ x u) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * intervalKernel R ψ x u)) := by
  exact left_integrals_tendsto R ψ x a hR ha hψ
    (interval_outer_integrable R ψ x a hR ha hψ)
    (fun N _ => sample_outer_integrable R N ψ x a ha)

end HVRPrimeLeftIntegrable
