import HVRCompactCorrelationQuadrature

/-! One-variable continuity and integrability candidates for the compact
autocorrelation and its sampled approximants. These proofs do not explicitly
invoke a convolution product theorem or an integral swap. External Lean
compilation, theorem-level axiom audit and dependency trace are required. -/

noncomputable section
open Filter MeasureTheory
open HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate
open HVRSpectralSeedCorrelation HVRSpectralCorrelationCompact
open HVRFrequencyIntervalCells HVRZetaHyperbolicFrequencyBounds
open HVRCompactCorrelationQuadrature
open scoped BigOperators Topology

namespace HVRCompactCorrelationRegularity

/-- Each actual correlation mode is integrable using only the compact support
of its first seed factor and one-variable continuity. -/
theorem seed_correlation_mode_integrable (w : ℝ) (hw : 0 < w) (t : ℝ) :
    Integrable (fun u : ℝ => complexSeed w hw u * complexSeed w hw (u - t)) := by
  have hf : Continuous (complexSeed w hw) := (complexSeed_smooth w hw).continuous
  have hcont : Continuous (fun u : ℝ => complexSeed w hw u *
      complexSeed w hw (u - t)) := hf.mul (hf.comp (continuous_id.sub continuous_const))
  have hcompact : HasCompactSupport (fun u : ℝ => complexSeed w hw u *
      complexSeed w hw (u - t)) := by
    exact (complexSeed_compact w hw).mul_right
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- Direct one-variable Lipschitz estimate for the actual compact
autocorrelation, with a supplied seed Lipschitz constant. -/
theorem complexCorrelation_frequency_lipschitz (w : ℝ) (hw : 0 < w)
    (t s L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ,
      ‖complexSeed w hw u - complexSeed w hw v‖ ≤ |u - v| * L) :
    ‖complexCorrelation w hw t - complexCorrelation w hw s‖ ≤
      (|t - s| * L) * ∫ u : ℝ, ‖complexSeed w hw u‖ := by
  have hf : Integrable (complexSeed w hw) :=
    (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
      (complexSeed_compact w hw)
  rw [complexCorrelation_eq_integral w hw t, complexCorrelation_eq_integral w hw s]
  apply HVRNativeDominatedLimit.integral_error_le_weighted (|t - s| * L)
    (seed_correlation_mode_integrable w hw t)
    (seed_correlation_mode_integrable w hw s) hf.norm
  filter_upwards [] with u
  calc
    ‖complexSeed w hw u * complexSeed w hw (u - t) -
        complexSeed w hw u * complexSeed w hw (u - s)‖ =
        ‖complexSeed w hw u‖ *
          ‖complexSeed w hw (u - t) - complexSeed w hw (u - s)‖ := by
            rw [← mul_sub, norm_mul]
    _ ≤ ‖complexSeed w hw u‖ * (|t - s| * L) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hLip (u - t) (u - s)
    _ = (|t - s| * L) * ‖complexSeed w hw u‖ := by ring

/-- The actual compact autocorrelation is continuous without using the
general convolution-continuity theorem. -/
theorem complexCorrelation_continuous_direct (w : ℝ) (hw : 0 < w) :
    Continuous (complexCorrelation w hw) := by
  obtain ⟨L, hL, hLip⟩ := complexSeed_exists_lipschitz w hw
  let B : ℝ := ∫ u : ℝ, ‖complexSeed w hw u‖
  have hB : 0 ≤ B := integral_nonneg (fun u => norm_nonneg _)
  let K : NNReal := ⟨L * B, mul_nonneg hL hB⟩
  have hcont : LipschitzWith K (complexCorrelation w hw) := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    change dist (complexCorrelation w hw t) (complexCorrelation w hw s) ≤
      (L * B) * dist t s
    have h := complexCorrelation_frequency_lipschitz w hw t s L hL hLip
    simpa only [dist_eq_norm, Real.norm_eq_abs, B, mul_assoc, mul_comm,
      mul_left_comm] using h
  exact hcont.continuous

/-- The exact correlation is integrable by compact support and the direct
one-variable continuity estimate. -/
theorem complexCorrelation_integrable_direct (w : ℝ) (hw : 0 < w) :
    Integrable (complexCorrelation w hw) :=
  (complexCorrelation_continuous_direct w hw).integrable_of_hasCompactSupport
    (complexCorrelation_hasCompactSupport w hw)

/-- Each finite-grid sampled correlation is continuous. -/
theorem sampledCorrelation_continuous (w : ℝ) (hw : 0 < w) (N : ℕ) :
    Continuous (sampledCorrelation w hw N) := by
  unfold sampledCorrelation
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul
    ((complexSeed_smooth w hw).continuous.comp (continuous_const.sub continuous_id))

/-- Each nonempty finite-grid sampled correlation has compact support. -/
theorem sampledCorrelation_hasCompactSupport (w : ℝ) (hw : 0 < w)
    (N : ℕ) (hN : 0 < N) : HasCompactSupport (sampledCorrelation w hw N) := by
  apply HasCompactSupport.intro (K := Set.Icc (-w) w) isCompact_Icc
  intro t ht
  apply sampledCorrelation_zero_of_band w hw N hN t
  by_contra hn
  have habs : |t| < w := lt_of_not_ge hn
  have ht' : t ∈ Set.Icc (-w) w := by
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  exact ht ht'

/-- The Fourier-modulated actual correlation is integrable without
appealing to the general convolution-integrability theorem. -/
theorem modulated_correlation_integrable (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    Integrable (fun t : ℝ => complexCorrelation w hw t * phase t ξ) := by
  have hphase : Continuous (fun t : ℝ => phase t ξ) := by
    unfold phase
    fun_prop
  have hcompact : HasCompactSupport (fun t : ℝ => complexCorrelation w hw t * phase t ξ) :=
    (complexCorrelation_hasCompactSupport w hw).mul_right
  exact ((complexCorrelation_continuous_direct w hw).mul hphase).integrable_of_hasCompactSupport
    hcompact

/-- The Fourier-modulated finite-grid correlation is also integrable. -/
theorem modulated_sampledCorrelation_integrable (w : ℝ) (hw : 0 < w)
    (N : ℕ) (hN : 0 < N) (ξ : ℝ) :
    Integrable (fun t : ℝ => sampledCorrelation w hw N t * phase t ξ) := by
  have hphase : Continuous (fun t : ℝ => phase t ξ) := by
    unfold phase
    fun_prop
  have hcompact : HasCompactSupport (fun t : ℝ => sampledCorrelation w hw N t * phase t ξ) :=
    (sampledCorrelation_hasCompactSupport w hw N hN).mul_right
  exact ((sampledCorrelation_continuous w hw N).mul hphase).integrable_of_hasCompactSupport
    hcompact

/-- No separate integrability assumptions are needed in the finite-grid
frequency-side convergence. -/
theorem sampled_frequency_integral_tendsto_interval_direct
    (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    Tendsto (fun N : ℕ => ∫ t : ℝ in Set.Ioc (-w) w,
      sampledCorrelation w hw N t * phase t ξ) atTop
      (𝓝 (∫ t : ℝ in Set.Ioc (-w) w, complexCorrelation w hw t * phase t ξ)) := by
  obtain ⟨L, hL, hLip⟩ := complexSeed_exists_lipschitz w hw
  apply sampled_frequency_integral_tendsto_interval w hw ξ L hL hLip
  · exact (modulated_correlation_integrable w hw ξ).mono_measure Measure.restrict_le_self
  · intro N hN
    exact (modulated_sampledCorrelation_integrable w hw N hN ξ).mono_measure
      Measure.restrict_le_self

/-- Outside the correlation band, the actual modulated correlation is zero. -/
theorem modulated_correlation_interval_eq_full (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    (∫ t : ℝ in Set.Ioc (-w) w, complexCorrelation w hw t * phase t ξ) =
      ∫ t : ℝ, complexCorrelation w hw t * phase t ξ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [] with t ht
  have hband : w ≤ |t| := by
    by_contra hn
    have habs : |t| < w := lt_of_not_ge hn
    exact ht ⟨(abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  simp only [complexCorrelation, Function.comp_apply,
    correlation_zero_of_band w hw t hband, Complex.ofReal_zero, zero_mul]

/-- The same whole-line restriction is valid for every nonempty sampled grid. -/
theorem modulated_sampled_interval_eq_full (w : ℝ) (hw : 0 < w)
    (N : ℕ) (hN : 0 < N) (ξ : ℝ) :
    (∫ t : ℝ in Set.Ioc (-w) w, sampledCorrelation w hw N t * phase t ξ) =
      ∫ t : ℝ, sampledCorrelation w hw N t * phase t ξ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [] with t ht
  have hband : w ≤ |t| := by
    by_contra hn
    have habs : |t| < w := lt_of_not_ge hn
    exact ht ⟨(abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  rw [sampledCorrelation_zero_of_band w hw N hN t hband, zero_mul]

/-- The sampled Fourier integrals converge to the actual whole-line
autocorrelation transform. -/
theorem sampled_frequency_integral_tendsto_full
    (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, sampledCorrelation w hw N t * phase t ξ)
      atTop (𝓝 (∫ t : ℝ, complexCorrelation w hw t * phase t ξ)) := by
  have h := sampled_frequency_integral_tendsto_interval_direct w hw ξ
  rw [modulated_correlation_interval_eq_full w hw ξ] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact modulated_sampled_interval_eq_full w hw N hN ξ

end HVRCompactCorrelationRegularity
