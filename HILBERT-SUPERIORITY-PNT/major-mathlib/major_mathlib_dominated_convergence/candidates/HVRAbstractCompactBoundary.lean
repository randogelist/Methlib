import NativeDominatedLimit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
An abstract one-dimensional compact-uniform integral-limit reduction. The
compact-uniform convergence and continuity of the boundary are explicit
hypotheses. This theorem, if audited, is not by itself the actual PNT result.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRAbstractCompactBoundary

def frequencyIntegrand (ψ : ℝ → ℂ) (x : ℝ) (F : ℕ → ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * F n t

def boundaryIntegrand (ψ : ℝ → ℂ) (x : ℝ) (G : ℝ → ℂ) (t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * G t

theorem norm_frequency_phase (t x : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Compact-uniform convergence passes through an integrable weight. -/
theorem frequency_integral_tendsto_boundary
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hψ : Integrable ψ volume)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ) (hG : Continuous G)
    (hconv : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ K, dist (F n t) (G t) < η)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x F n) volume) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x F n t)
      atTop (𝓝 (∫ t : ℝ, boundaryIntegrand ψ x G t)) := by
  have hw : Integrable (fun t : ℝ => ‖ψ t‖) volume := hψ.norm
  have hW : 0 ≤ ∫ t : ℝ, ‖ψ t‖ := integral_nonneg fun t => norm_nonneg _
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have he : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
    fun_prop
  have hmeasG : AEStronglyMeasurable (boundaryIntegrand ψ x G) volume := by
    exact (hψ.aestronglyMeasurable.mul he.aestronglyMeasurable).mul
      hG.aestronglyMeasurable
  have hmajorG : Integrable (fun t : ℝ => (|B| + 1) * ‖ψ t‖) volume :=
    hw.const_mul (|B| + 1)
  have hg : Integrable (boundaryIntegrand ψ x G) volume := by
    apply hmajorG.mono' hmeasG
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [boundaryIntegrand, ht]
    · have hBt : ‖G t‖ ≤ |B| + 1 := by
        have h0 := hB t (hsupport t ht)
        linarith [le_abs_self B]
      have hm := mul_le_mul_of_nonneg_left hBt (norm_nonneg (ψ t))
      simp only [boundaryIntegrand, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let W : ℝ := ∫ t : ℝ, ‖ψ t‖
  let η : ℝ := ε / (W + 1)
  have hW' : 0 ≤ W := hW
  have hden : 0 < W + 1 := by linarith
  have hη : 0 < η := by dsimp [η]; exact div_pos hε hden
  have hsmall : η * W < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    have hmul : ε * W < ε * (W + 1) :=
      mul_lt_mul_of_pos_left (by linarith : W < W + 1) hε
    nlinarith
  filter_upwards [hconv η hη] with n hn
  have hnear (t : ℝ) (ht : t ∈ K) : ‖F n t - G t‖ < η := by
    simpa only [dist_eq_norm] using hn t ht
  have hmajorF : Integrable (fun t : ℝ => (|B| + η + 1) * ‖ψ t‖) volume :=
    hw.const_mul (|B| + η + 1)
  have hf : Integrable (frequencyIntegrand ψ x F n) volume := by
    apply hmajorF.mono' (hmeas n)
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [frequencyIntegrand, ht]
    · have htK := hsupport t ht
      have hBt := hB t htK
      have htri : ‖F n t‖ ≤ ‖F n t - G t‖ + ‖G t‖ := by
        calc
          ‖F n t‖ = ‖(F n t - G t) + G t‖ := by simp
          _ ≤ _ := norm_add_le _ _
      have hF : ‖F n t‖ ≤ |B| + η + 1 := by linarith [hnear t htK, le_abs_self B]
      have hm := mul_le_mul_of_nonneg_left hF (norm_nonneg (ψ t))
      simp only [frequencyIntegrand, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
  have hbound : ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x F n t - boundaryIntegrand ψ x G t‖ ≤ η * ‖ψ t‖ := by
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [frequencyIntegrand, boundaryIntegrand, ht]
    · have hfactor : frequencyIntegrand ψ x F n t - boundaryIntegrand ψ x G t =
          (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * (F n t - G t) := by
        simp only [frequencyIntegrand, boundaryIntegrand]
        ring
      have hm := mul_le_mul_of_nonneg_left (le_of_lt (hnear t (hsupport t ht)))
        (norm_nonneg (ψ t))
      rw [hfactor, norm_mul, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
  have herror := HVRNativeDominatedLimit.integral_error_le_weighted η hf hg hw hbound
  have hfinal : ‖(∫ t : ℝ, frequencyIntegrand ψ x F n t) -
      (∫ t : ℝ, boundaryIntegrand ψ x G t)‖ < ε :=
    lt_of_le_of_lt herror hsmall
  simpa only [dist_eq_norm] using hfinal

end HVRAbstractCompactBoundary
