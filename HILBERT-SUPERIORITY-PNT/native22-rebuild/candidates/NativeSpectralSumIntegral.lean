import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic
import NativeExpIntegral

/-!
Candidate nonnegative sum/integral bridge via extended nonnegative integration.
It keeps the real series integrability, almost-everywhere pointwise summability,
and summability of mode integrals as explicit hypotheses. These hypotheses are
not yet discharged here from a summable spectral mass. Compilation, named axiom
audits and recursive theorem-dependency inspection remain outstanding.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NativeSpectralSumIntegral

/-- A nonnegative real series can be exchanged with an integral when both
sides are known to be integrable/summable and the pointwise series converges
almost everywhere. The proof passes through Tonelli for `ℝ≥0∞`. -/
theorem nonnegative_integral_tsum
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ)
    (hpos : ∀ n x, 0 ≤ f n x)
    (hi : ∀ n, Integrable (f n) μ)
    (hfi : Integrable (fun x => ∑' n, f n x) μ)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => f n x))
    (hsi : Summable (fun n => ∫ x, f n x ∂μ)) :
    (∫ x, ∑' n, f n x ∂μ) = ∑' n, ∫ x, f n x ∂μ := by
  have hn : ∀ x, 0 ≤ ∑' n, f n x := fun x => tsum_nonneg (fun n => hpos n x)
  have hi_nonneg : ∀ n, 0 ≤ ∫ x, f n x ∂μ :=
    fun n => integral_nonneg (fun x => hpos n x)
  have hleft : 0 ≤ ∫ x, ∑' n, f n x ∂μ := integral_nonneg hn
  have hright : 0 ≤ ∑' n, ∫ x, f n x ∂μ := tsum_nonneg hi_nonneg
  have he : ENNReal.ofReal (∫ x, ∑' n, f n x ∂μ) =
      ENNReal.ofReal (∑' n, ∫ x, f n x ∂μ) := by
    calc
      ENNReal.ofReal (∫ x, ∑' n, f n x ∂μ) =
          ∫⁻ x, ENNReal.ofReal (∑' n, f n x) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all μ hn)
      _ = ∫⁻ x, ∑' n, ENNReal.ofReal (f n x) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hs] with x hx
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => hpos n x) hx
      _ = ∑' n, ∫⁻ x, ENNReal.ofReal (f n x) ∂μ := by
        apply lintegral_tsum
        intro n
        exact ENNReal.measurable_ofReal.comp_aemeasurable (hi n).aestronglyMeasurable.aemeasurable
      _ = ∑' n, ENNReal.ofReal (∫ x, f n x ∂μ) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_eq_lintegral_ofReal (hi n)
          (ae_of_all μ (fun x => hpos n x))).symm
      _ = ENNReal.ofReal (∑' n, ∫ x, f n x ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg hi_nonneg hsi).symm
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hleft, ENNReal.toReal_ofReal hright] using ht

/-- Spectral-mode interchange for nonnegative weights. Explicit residual
hypotheses concern integrability of the summed mode, pointwise summability,
and summability of the integrals. -/
theorem nonnegative_spectral_mode_interchange
    (weight energy : ℕ → ℝ) (w : ℝ)
    (hw : ∀ n, 0 ≤ weight n)
    (hpos : ∀ n, 0 < w + energy n)
    (hfi : IntegrableOn (fun t : ℝ =>
      ∑' n, weight n * Real.exp (-(w + energy n) * t)) (Set.Ioi 0) volume)
    (hs : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Summable (fun n => weight n * Real.exp (-(w + energy n) * t)))
    (hsi : Summable (fun n =>
      ∫ t : ℝ in Set.Ioi 0, weight n * Real.exp (-(w + energy n) * t))) :
    (∫ t : ℝ in Set.Ioi 0,
      ∑' n, weight n * Real.exp (-(w + energy n) * t)) =
      ∑' n, ∫ t : ℝ in Set.Ioi 0,
        weight n * Real.exp (-(w + energy n) * t) := by
  apply nonnegative_integral_tsum
    (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun n t => weight n * Real.exp (-(w + energy n) * t))
  · intro n t
    exact mul_nonneg (hw n) (le_of_lt (Real.exp_pos _))
  · intro n
    exact NativeExpIntegral.mode_integrable (weight n) (energy n) w (hpos n)
  · exact hfi
  · exact hs
  · exact hsi

end NativeSpectralSumIntegral
