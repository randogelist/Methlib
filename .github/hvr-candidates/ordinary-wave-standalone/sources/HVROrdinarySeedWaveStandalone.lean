import HVRStandaloneSeedIntervalDecay
import HVRAnalyticPhaseBasics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.FourierTransform

/-! Candidate ordinary-integral wave for the compact HVR seed. The wave is
defined directly as a one-dimensional integral rather than as an inverse
Fourier transform on Schwartz space. The global bound, first moment and
continuity below are elementary consequences of integrability and the finite-
interval derivative estimate. The proposed square-integrability proof uses
an explicit integrable majorant. PNT-root replacement is not established.
No local Lean execution was performed; external compilation, axiom audits and
swap tracing are needed. -/

noncomputable section
open Filter MeasureTheory
open HVROrdinarySeed HVRAnalyticPhaseBasics
open HVRStandaloneSeedIntervalDecay
open scoped Topology

namespace HVROrdinarySeedWave

/-- The physical wave defined directly as an ordinary phase integral. -/
def ordinaryWave (w : ℝ) (hw : 0 < w) (x : ℝ) : ℂ :=
  ∫ t : ℝ, complexSeed w hw t * phase t (-(2 * Real.pi * x))

/-- The standalone phase definition is exactly Mathlib's ordinary inverse
Fourier integral, with the 2π convention made explicit. -/
theorem ordinaryWave_eq_fourierInv (w : ℝ) (hw : 0 < w) (x : ℝ) :
    ordinaryWave w hw x = FourierTransformInv.fourierInv (complexSeed w hw) x := by
  symm
  rw [Real.fourierInv_eq']
  unfold ordinaryWave
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Real.inner_apply, smul_eq_mul]
  have hphase : Complex.exp (((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I) =
      phase t (-(2 * Real.pi * x)) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [hphase, mul_comm]

theorem seed_integrable (w : ℝ) (hw : 0 < w) : Integrable (complexSeed w hw) :=
  (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
    (complexSeed_compact w hw)

/-- Compact support supplies the seed's first absolute moment. -/
theorem seed_first_moment_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (fun t : ℝ => |t| * ‖complexSeed w hw t‖) := by
  have hcont : Continuous (fun t : ℝ => |t| * ‖complexSeed w hw t‖) :=
    continuous_id.abs.mul ((complexSeed_smooth w hw).continuous.norm)
  have hcompact : HasCompactSupport (fun t : ℝ => |t| * ‖complexSeed w hw t‖) :=
    (complexSeed_compact w hw).norm.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The direct wave is bounded by the seed's L1 mass. -/
theorem ordinaryWave_norm_le (w : ℝ) (hw : 0 < w) (x : ℝ) :
    ‖ordinaryWave w hw x‖ ≤ ∫ t : ℝ, ‖complexSeed w hw t‖ := by
  unfold ordinaryWave
  apply norm_integral_le_of_norm_le (seed_integrable w hw).norm
  filter_upwards [] with t
  have hp : ‖phase t (-(2 * Real.pi * x))‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp only [norm_mul, hp, mul_one, le_refl]

/-- Direct continuity follows from a one-variable first-moment Lipschitz
estimate for the phase integral. -/
theorem ordinaryWave_continuous (w : ℝ) (hw : 0 < w) :
    Continuous (ordinaryWave w hw) := by
  let M : ℝ := ∫ t : ℝ, |t| * ‖complexSeed w hw t‖
  have hM : 0 ≤ M := integral_nonneg (fun t => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  have hmode (ξ : ℝ) : Integrable (fun t : ℝ => complexSeed w hw t * phase ξ t) := by
    have h := phase_mul_integrable (complexSeed w hw) ξ (seed_integrable w hw)
    simpa only [HVRAnalyticPhaseBasics.phase_symm] using h
  let K : NNReal := ⟨(2 * Real.pi) * M, mul_nonneg (by positivity) hM⟩
  have hL : LipschitzWith K (ordinaryWave w hw) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (ordinaryWave w hw x) (ordinaryWave w hw y) ≤
      ((2 * Real.pi) * M) * dist x y
    have h := integral_phase_frequency_lipschitz (complexSeed w hw)
      (-(2 * Real.pi * x)) (-(2 * Real.pi * y))
      (hmode _) (hmode _)
      (seed_first_moment_integrable w hw)
    have habs : |-(2 * Real.pi * x) - -(2 * Real.pi * y)| =
        (2 * Real.pi) * |x - y| := by
      have heq : -(2 * Real.pi * x) - -(2 * Real.pi * y) =
          -(2 * Real.pi) * (x - y) := by ring
      rw [heq, abs_mul, abs_neg, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
    rw [habs] at h
    simpa only [ordinaryWave, HVRAnalyticPhaseBasics.phase_symm,
      dist_eq_norm, Real.norm_eq_abs, M,
      mul_assoc, mul_comm, mul_left_comm] using h
  exact hL.continuous

/-- The 1D integration-by-parts bound gives 1/|x| decay of the direct wave. -/
theorem ordinaryWave_first_derivative_bound (w : ℝ) (hw : 0 < w) (x : ℝ) :
    |x| * ‖ordinaryWave w hw x‖ ≤
      (∫ t : ℝ, ‖deriv (complexSeed w hw) t‖) / (2 * Real.pi) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := seed_phase_first_derivative_bound w hw (-(2 * Real.pi * x))
  have habs : |-(2 * Real.pi * x)| = (2 * Real.pi) * |x| := by
    rw [abs_neg, abs_mul, abs_of_pos hπ]
  rw [habs] at h
  change ((2 * Real.pi) * |x|) * ‖ordinaryWave w hw x‖ ≤
    ∫ t : ℝ, ‖deriv (complexSeed w hw) t‖ at h
  apply (le_div_iff₀ hπ).2
  nlinarith

/-- The square of the direct wave has an integrable one-dimensional
majorant, obtained from the L1 bound and the derivative decay estimate. -/
theorem ordinaryWave_norm_sq_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (fun x : ℝ => ‖ordinaryWave w hw x‖ ^ 2) := by
  let B : ℝ := ∫ t : ℝ, ‖complexSeed w hw t‖
  let D : ℝ := ∫ t : ℝ, ‖deriv (complexSeed w hw) t‖
  let C : ℝ := B ^ 2 + (D / (2 * Real.pi)) ^ 2
  have hB : 0 ≤ B := integral_nonneg (fun t => norm_nonneg _)
  have hD : 0 ≤ D := integral_nonneg (fun t => norm_nonneg _)
  have hπ : 0 < 2 * Real.pi := by positivity
  have hmajor : Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖ordinaryWave w hw x‖ ^ 2) :=
    ((ordinaryWave_continuous w hw).norm.pow 2).measurable.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [] with x
  have hW : 0 ≤ ‖ordinaryWave w hw x‖ := norm_nonneg _
  have hWB : ‖ordinaryWave w hw x‖ ≤ B := ordinaryWave_norm_le w hw x
  have hWD : |x| * ‖ordinaryWave w hw x‖ ≤ D / (2 * Real.pi) :=
    ordinaryWave_first_derivative_bound w hw x
  have hW2 : ‖ordinaryWave w hw x‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hW hB).2 hWB
  have hDq : 0 ≤ D / (2 * Real.pi) := div_nonneg hD (le_of_lt hπ)
  have hDx2 : x ^ 2 * ‖ordinaryWave w hw x‖ ^ 2 ≤ (D / (2 * Real.pi)) ^ 2 := by
    have h := (sq_le_sq₀ (mul_nonneg (abs_nonneg x) hW) hDq).2 hWD
    simpa only [mul_pow, sq_abs] using h
  have htotal : ‖ordinaryWave w hw x‖ ^ 2 * (1 + x ^ 2) ≤ C := by
    dsimp [C]
    nlinarith
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hpoint : ‖ordinaryWave w hw x‖ ^ 2 ≤ C * (1 + x ^ 2)⁻¹ :=
    (le_mul_inv_iff₀ hpos).2 htotal
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ordinaryWave w hw x‖)]
  exact hpoint

end HVROrdinarySeedWave
