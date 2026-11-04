import HVRPrimeLeftQuadrature
import HVR_SpectralCorrelation_Compact
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
Compact-seed autocorrelation approximation by finite frequency cells.

The approximation freezes the translated seed in each cell and weights it
with the exact cell integral of the original seed. The resulting pointwise
error is uniform in the correlation variable. This module does not yet
integrate that error in the Fourier variable, prove the transform-square
identity, or establish independence from any transitive dependency.

Lean source candidate: no local Lean run, external build, named theorem audit,
or theorem-level dependency trace has yet been performed.
-/

noncomputable section
open Filter MeasureTheory
open HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate
open HVRSpectralSeedCorrelation HVRSpectralCorrelationCompact
open HVRFrequencyIntervalCells
open scoped BigOperators Topology

namespace HVRCompactCorrelationQuadrature

/-- Smooth compactly supported seed has a finite global Lipschitz bound. -/
theorem complexSeed_exists_lipschitz (w : ℝ) (hw : 0 < w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u v : ℝ,
      ‖complexSeed w hw u - complexSeed w hw v‖ ≤ |u - v| * L := by
  obtain ⟨C, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (complexSeed_compact w hw) (complexSeed_smooth w hw) (by simp)
  refine ⟨(C : ℝ), NNReal.coe_nonneg C, ?_⟩
  intro u v
  have h := hLip.dist_le_mul u v
  simpa only [dist_eq_norm, Real.norm_eq_abs, mul_comm] using h

/-- The exact seed cell weights coupled with the frozen translated seed. -/
def sampledCorrelation (w : ℝ) (hw : 0 < w) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (∫ u : ℝ in gridCell (w / 2) N i, complexSeed w hw u) *
      complexSeed w hw (gridPoint (w / 2) N i - t)

/-- The complex autocorrelation is the ordinary one-variable integral of
the two complex-valued seed factors. -/
theorem complexCorrelation_eq_integral (w : ℝ) (hw : 0 < w) (t : ℝ) :
    complexCorrelation w hw t =
      ∫ u : ℝ, complexSeed w hw u * complexSeed w hw (u - t) := by
  change (((∫ u : ℝ, seed w hw u * seed w hw (u - t)) : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [complexSeed, Function.comp_apply, Complex.ofReal_mul]

/-- The seed vanishes outside the exact half-open frequency interval. -/
theorem complexSeed_zero_off_interval (w : ℝ) (hw : 0 < w) (u : ℝ)
    (hu : u ∉ Set.Ioc (-(w / 2)) (w / 2)) : complexSeed w hw u = 0 := by
  have hband : w / 2 ≤ |u| := by
    by_contra h
    have hlt : |u| < w / 2 := lt_of_not_ge h
    have hu' := abs_lt.mp hlt
    apply hu
    exact ⟨hu'.1, le_of_lt hu'.2⟩
  simp only [complexSeed, Function.comp_apply, seed_zero_of_band w hw u hband,
    Complex.ofReal_zero]

/-- Uniform pointwise finite-cell approximation for the actual seed
autocorrelation. L is any nonnegative global Lipschitz constant for the seed. -/
theorem complexCorrelation_grid_error_of_lipschitz
    (w : ℝ) (hw : 0 < w) (N : ℕ) (hN : 0 < N) (t L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ,
      ‖complexSeed w hw u - complexSeed w hw v‖ ≤ |u - v| * L) :
    ‖complexCorrelation w hw t - sampledCorrelation w hw N t‖ ≤
      ((2 * (w / 2) / (N : ℝ)) * L) *
        ∫ u : ℝ, ‖complexSeed w hw u‖ := by
  let R : ℝ := w / 2
  let φ : ℝ → ℂ := complexSeed w hw
  let T : ℝ → ℂ := fun u => complexSeed w hw (u - t)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hδ : 0 ≤ 2 * R / (N : ℝ) := by positivity
  have hφ : Integrable φ :=
    (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
      (complexSeed_compact w hw)
  have hT : Continuous T := by
    exact (complexSeed_smooth w hw).continuous.comp (continuous_id.sub continuous_const)
  have hLipT : ∀ u v : ℝ, ‖T u - T v‖ ≤ |u - v| * L := by
    intro u v
    simpa only [T, sub_sub_sub_cancel_right] using hLip (u - t) (v - t)
  have hf : ∀ i ∈ Finset.range N, IntegrableOn
      (fun u : ℝ => φ u * T u) (gridCell R N i) := by
    intro i hi
    exact HVRPrimeGridIntegrability.weighted_lipschitz_integrable_on_cell
      (gridCell R N i) φ T (gridPoint R N i) (2 * R / (N : ℝ)) L hδ hL
      hT hLipT hφ (gridCells_close_ae R N i hi)
  have hg : ∀ i ∈ Finset.range N, IntegrableOn
      (fun u : ℝ => φ u * T (gridPoint R N i)) (gridCell R N i) := by
    intro i hi
    exact (hφ.mono_measure Measure.restrict_le_self).mul_const _
  have h := HVRFrequencyTransformGrid.finite_cells_lipschitz_error
    (Finset.range N) (gridCell R N) φ T (gridPoint R N) (2 * R / (N : ℝ)) L
    hδ hL hLipT hφ (fun i hi => gridCells_measurable R N i)
    (gridCells_pairwise_disjoint R N hR) hf hg (gridCells_close_ae R N)
  have hunion := integral_biUnion_finset (μ := volume) (f := fun u : ℝ => φ u * T u)
    (Finset.range N) (fun i hi => gridCells_measurable R N i)
    (gridCells_pairwise_disjoint R N hR) hf
  rw [HVRPrimeLeftQuadrature.gridCells_eq_Ioc R N hR hN] at hunion
  have hfull : (∫ u : ℝ in Set.Ioc (-R) R, φ u * T u) =
      ∫ u : ℝ, φ u * T u := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with u hu
    have hz : complexSeed w hw u = 0 := by
      apply complexSeed_zero_off_interval w hw u
      simpa only [R] using hu
    simp only [φ, hz, zero_mul]
  have hsample : (∑ i ∈ Finset.range N,
      ∫ u : ℝ in gridCell R N i, φ u * T (gridPoint R N i)) =
      sampledCorrelation w hw N t := by
    unfold sampledCorrelation
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const]
  rw [Finset.sum_sub_distrib, ← hunion, hfull, hsample] at h
  simpa only [R, φ, T, complexCorrelation_eq_integral] using h

/-- Every grid point used by the sampled correlation lies in the seed band. -/
theorem sample_abs_le_half_band (w : ℝ) (hw : 0 < w)
    (N i : ℕ) (hN : 0 < N) (hi : i ∈ Finset.range N) :
    |gridPoint (w / 2) N i| ≤ w / 2 := by
  have hR : 0 ≤ w / 2 := by positivity
  have hleft : -(w / 2) ≤ gridPoint (w / 2) N i := by
    simpa only [gridPoint_zero] using
      gridPoint_monotone (w / 2) N hR (Nat.zero_le i)
  have hright : gridPoint (w / 2) N i ≤ w / 2 := by
    have hiN : i ≤ N := le_of_lt (Finset.mem_range.mp hi)
    simpa only [gridPoint_end (w / 2) N hN] using
      gridPoint_monotone (w / 2) N hR hiN
  exact abs_le.mpr ⟨hleft, hright⟩

/-- The sampled correlation stays inside the same band as the true one. -/
theorem sampledCorrelation_zero_of_band (w : ℝ) (hw : 0 < w)
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : w ≤ |t|) :
    sampledCorrelation w hw N t = 0 := by
  unfold sampledCorrelation
  apply Finset.sum_eq_zero
  intro i hi
  have hs := sample_abs_le_half_band w hw N i hN hi
  have hband : w / 2 ≤ |gridPoint (w / 2) N i - t| := by
    by_contra h
    have hdiff := abs_lt.mp (lt_of_not_ge h)
    have hsample := abs_le.mp hs
    have htt : -w < t ∧ t < w := by constructor <;> linarith
    have habs : |t| < w := abs_lt.mpr htt
    linarith
  simp only [complexSeed, Function.comp_apply, seed_zero_of_band w hw _ hband,
    Complex.ofReal_zero, mul_zero]

/-- After the uniform cell estimate, a one-dimensional integral norm bound
gives a quantitative error over the band. The two integrabilities are
explicit hypotheses and must still be proved without importing Fubini. -/
theorem frequency_interval_error_of_lipschitz
    (w : ℝ) (hw : 0 < w) (N : ℕ) (hN : 0 < N) (ξ L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ,
      ‖complexSeed w hw u - complexSeed w hw v‖ ≤ |u - v| * L)
    (hfull : IntegrableOn
      (fun t : ℝ => complexCorrelation w hw t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ) (Set.Ioc (-w) w))
    (happrox : IntegrableOn
      (fun t : ℝ => sampledCorrelation w hw N t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ) (Set.Ioc (-w) w)) :
    ‖(∫ t : ℝ in Set.Ioc (-w) w, complexCorrelation w hw t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ) -
      (∫ t : ℝ in Set.Ioc (-w) w, sampledCorrelation w hw N t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ)‖ ≤
      (((2 * (w / 2) / (N : ℝ)) * L) *
        ∫ u : ℝ, ‖complexSeed w hw u‖) *
        ∫ _t : ℝ in Set.Ioc (-w) w, (1 : ℝ) := by
  let E : ℝ := ((2 * (w / 2) / (N : ℝ)) * L) *
    ∫ u : ℝ, ‖complexSeed w hw u‖
  have hone : IntegrableOn (fun _t : ℝ => (1 : ℝ)) (Set.Ioc (-w) w) :=
    integrableOn_const measure_Ioc_lt_top.ne
  apply HVRNativeDominatedLimit.integral_error_le_weighted E hfull happrox hone
  filter_upwards [] with t
  have hp : ‖HVRZetaHyperbolicFrequencyBounds.phase t ξ‖ = 1 := by
    simp [HVRZetaHyperbolicFrequencyBounds.phase, Complex.norm_exp,
      Complex.mul_re, Complex.mul_im]
  calc
    ‖complexCorrelation w hw t * HVRZetaHyperbolicFrequencyBounds.phase t ξ -
        sampledCorrelation w hw N t * HVRZetaHyperbolicFrequencyBounds.phase t ξ‖ =
        ‖complexCorrelation w hw t - sampledCorrelation w hw N t‖ := by
          rw [← sub_mul, norm_mul, hp, mul_one]
    _ ≤ E := complexCorrelation_grid_error_of_lipschitz w hw N hN t L hL hLip
    _ = E * (1 : ℝ) := (mul_one E).symm

/-- Conditional frequency-side convergence, with the two one-dimensional
integrability obligations kept explicit. -/
theorem sampled_frequency_integral_tendsto_interval
    (w : ℝ) (hw : 0 < w) (ξ L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ,
      ‖complexSeed w hw u - complexSeed w hw v‖ ≤ |u - v| * L)
    (hfull : IntegrableOn
      (fun t : ℝ => complexCorrelation w hw t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ) (Set.Ioc (-w) w))
    (happrox : ∀ N : ℕ, 0 < N → IntegrableOn
      (fun t : ℝ => sampledCorrelation w hw N t *
        HVRZetaHyperbolicFrequencyBounds.phase t ξ) (Set.Ioc (-w) w)) :
    Tendsto (fun N : ℕ => ∫ t : ℝ in Set.Ioc (-w) w,
      sampledCorrelation w hw N t * HVRZetaHyperbolicFrequencyBounds.phase t ξ)
      atTop (𝓝 (∫ t : ℝ in Set.Ioc (-w) w,
        complexCorrelation w hw t * HVRZetaHyperbolicFrequencyBounds.phase t ξ)) := by
  apply HVRFrequencyMeshLimit.tendsto_of_grid_error (w / 2)
    ((L * ∫ u : ℝ, ‖complexSeed w hw u‖) *
      ∫ _t : ℝ in Set.Ioc (-w) w, (1 : ℝ))
  intro N hN
  have h := frequency_interval_error_of_lipschitz w hw N hN ξ L hL hLip
    hfull (happrox N hN)
  rw [norm_sub_rev]
  convert h using 1 <;> ring

end HVRCompactCorrelationQuadrature
