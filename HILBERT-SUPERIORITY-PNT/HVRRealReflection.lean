import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! Candidate one-dimensional reflection and affine change of variables.
The proof specializes the scalar transformation of real Lebesgue measure,
instead of invoking the generic Haar negation-invariance instance. It has not
yet passed external Lean or theorem-level axiom/dependency checks. -/

noncomputable section
open MeasureTheory

namespace HVRRealReflection

/-- Negation preserves real Lebesgue measure by the one-dimensional scalar
map formula. -/
theorem neg_measurePreserving :
    MeasurePreserving (fun u : ℝ => -u) volume volume := by
  refine ⟨measurable_neg, ?_⟩
  have h := Real.map_volume_mul_left (show (-1 : ℝ) ≠ 0 by norm_num)
  simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one,
    ENNReal.ofReal_one, one_smul] using h

/-- The generic negation-invariance class, supplied by the direct real proof. -/
theorem real_volume_negInvariant_direct : (volume : Measure ℝ).IsNegInvariant := by
  constructor
  change Measure.map (fun u : ℝ => -u) (volume : Measure ℝ) = volume
  exact neg_measurePreserving.map_eq

/-- Reflection about an arbitrary real point preserves Lebesgue measure. -/
theorem subLeft_measurePreserving (x : ℝ) :
    MeasurePreserving (fun u : ℝ => x - u) volume volume := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) x).comp neg_measurePreserving
  simpa only [Function.comp_def, sub_eq_add_neg] using h

theorem subLeft_measurableEmbedding (x : ℝ) :
    MeasurableEmbedding (fun u : ℝ => x - u) := by
  change MeasurableEmbedding (fun u : ℝ => x + -u)
  exact ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft x)).measurableEmbedding

/-- Integrability is preserved by the explicit one-dimensional reflection. -/
theorem integrable_subLeft (f : ℝ → ℝ) (x : ℝ) (hf : Integrable f volume) :
    Integrable (fun u : ℝ => f (x - u)) volume := by
  simpa only [Function.comp_def] using
    ((subLeft_measurePreserving x).integrable_comp_emb (subLeft_measurableEmbedding x)).mpr hf

/-- Change of variables for the explicit one-dimensional reflection. -/
theorem integral_subLeft (f : ℝ → ℝ) (x : ℝ) :
    (∫ u : ℝ, f (x - u)) = ∫ u : ℝ, f u := by
  exact (subLeft_measurePreserving x).integral_comp (subLeft_measurableEmbedding x) f

theorem integrable_neg (f : ℝ → ℝ) (hf : Integrable f volume) :
    Integrable (fun u : ℝ => f (-u)) volume := by
  simpa only [Function.comp_def] using
    (neg_measurePreserving.integrable_comp_emb (Homeomorph.neg ℝ).measurableEmbedding).mpr hf

end HVRRealReflection
