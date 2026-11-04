import HVRCompactSeedPhaseGrid
import HVRPhaseTranslationDirect

/-!
Finite-sum Fourier factorization for the sampled compact autocorrelation.
The proof is a finite sum of one-dimensional changes of variables and does not
invoke a two-variable integral swap or the Fourier convolution theorem.
Lean compilation, named-theorem axiom audit, and transitive trace are pending.
-/

noncomputable section
open Filter MeasureTheory
open HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate
open HVRFrequencyIntervalCells HVRZetaHyperbolicFrequencyBounds
open HVRCompactCorrelationQuadrature HVRCompactSeedPhaseGrid
open HVRPrimeLeftQuadrature HVRPhaseTranslationDirect
open scoped BigOperators Topology

namespace HVRCompactCorrelationPhaseSum

/-- The actual complex seed inherits evenness from its real seed. -/
theorem complexSeed_even (w : ℝ) (hw : 0 < w) (t : ℝ) :
    complexSeed w hw (-t) = complexSeed w hw t := by
  simp only [complexSeed, Function.comp_apply, seed_even]

/-- Every sampled Fourier mode is integrable by a one-variable translation. -/
theorem translated_seed_phase_integrable (w : ℝ) (hw : 0 < w) (s x : ℝ) :
    Integrable (fun t : ℝ => complexSeed w hw (t - s) * phase t x) := by
  have hf : Integrable (complexSeed w hw) :=
    (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
      (complexSeed_compact w hw)
  exact phase_mul_integrable (fun t : ℝ => complexSeed w hw (t - s)) x
    (hf.comp_sub_right s)

/-- After finitely many one-variable translations, the Fourier transform
of the sampled correlation is the seed transform times its sampled phase
sum. -/
theorem sampled_phase_integral_eq_product (w : ℝ) (hw : 0 < w)
    (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (∫ t : ℝ in Set.Ioc (-w) w, sampledCorrelation w hw N t * phase t x) =
      sampledPhase w hw N x * ∫ t : ℝ, complexSeed w hw t * phase t x := by
  have hfull : (∫ t : ℝ in Set.Ioc (-w) w,
      sampledCorrelation w hw N t * phase t x) =
      ∫ t : ℝ, sampledCorrelation w hw N t * phase t x := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with t ht
    have hband : w ≤ |t| := by
      by_contra hn
      have hlt : |t| < w := lt_of_not_ge hn
      have ht' := abs_lt.mp hlt
      exact ht ⟨ht'.1, le_of_lt ht'.2⟩
    rw [sampledCorrelation_zero_of_band w hw N hN t hband, zero_mul]
  rw [hfull]
  have heq : (fun t : ℝ => sampledCorrelation w hw N t * phase t x) =
      (fun t : ℝ => ∑ i ∈ Finset.range N,
        (∫ u : ℝ in gridCell (w / 2) N i, complexSeed w hw u) *
          (complexSeed w hw (t - gridPoint (w / 2) N i) * phase t x)) := by
    funext t
    unfold sampledCorrelation
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have heven : complexSeed w hw (gridPoint (w / 2) N i - t) =
        complexSeed w hw (t - gridPoint (w / 2) N i) := by
      rw [show gridPoint (w / 2) N i - t = -(t - gridPoint (w / 2) N i) by ring,
        complexSeed_even]
    rw [heven]
    ring
  rw [heq]
  rw [integral_finsetSum (Finset.range N)
    (fun i hi => (translated_seed_phase_integrable w hw (gridPoint (w / 2) N i) x).const_mul _)]
  simp_rw [integral_const_mul, translated_phase_integral]
  unfold sampledPhase
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The sampled autocorrelation's band integrals tend to the square of the
one-variable seed phase integral. -/
theorem sampled_phase_integrals_tendsto_square
    (w : ℝ) (hw : 0 < w) (x : ℝ) :
    Tendsto (fun N : ℕ => ∫ t : ℝ in Set.Ioc (-w) w,
      sampledCorrelation w hw N t * phase t x) atTop
      (𝓝 ((∫ t : ℝ, complexSeed w hw t * phase t x) ^ 2)) := by
  let F : ℂ := ∫ t : ℝ, complexSeed w hw t * phase t x
  have hprod : Tendsto (fun N : ℕ => sampledPhase w hw N x * F) atTop (𝓝 (F * F)) :=
    (sampledPhase_tendsto w hw x).mul_const F
  have heventual : ∀ᶠ N : ℕ in atTop,
      (∫ t : ℝ in Set.Ioc (-w) w, sampledCorrelation w hw N t * phase t x) =
        sampledPhase w hw N x * F := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact sampled_phase_integral_eq_product w hw N hN x
  have hlim := hprod.congr' heventual.symm
  simpa only [F, pow_two] using hlim

end HVRCompactCorrelationPhaseSum
