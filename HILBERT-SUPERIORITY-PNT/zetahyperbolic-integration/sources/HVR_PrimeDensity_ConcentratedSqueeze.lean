import HVR_PrimeDensity_WindowBridge
import HVR_Positive_SmoothingSqueeze
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Filter MeasureTheory
open HVRPrimeLogDensity HVRPrimeDensityWindowBridge
open HVRPrimeDensityWeightedIntegrability HVRPositiveSmoothingSqueeze
open scoped Topology

/-!
Candidate conditional bridge from actual prime-density window estimates to
the existing generic smoothing squeeze. Kernel existence, its Fourier
properties and the two full convolution limits are explicit hypotheses and
are not proved here. No local Lean run was performed.
-/
namespace HVRPrimeDensityConcentratedSqueeze

/-- A forward kernel average of the actual normalized log-prime count. -/
def forwardSmooth (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v : ℝ in Set.univ, k v * logPrimeDensity (x + v)

/-- The reflected kernel average of the same actual prime density. -/
def backwardSmooth (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ v : ℝ in Set.univ, k v * logPrimeDensity (x - v)

/-- Split a full integral into a finite positive window and its complement. -/
theorem integral_split_window (f : ℝ → ℝ) (h : ℝ)
    (hf : IntegrableOn f Set.univ volume) :
    (∫ v : ℝ in Set.univ, f v) =
      (∫ v : ℝ in Set.Icc 0 h, f v) +
        (∫ v : ℝ in (Set.Icc 0 h)ᶜ, f v) := by
  have hd : Disjoint (Set.Icc (0 : ℝ) h) (Set.Icc 0 h)ᶜ := by
    apply Set.disjoint_left.mpr
    intro v hv hv'
    exact hv' hv
  have hwin : IntegrableOn f (Set.Icc 0 h) volume :=
    hf.mono_set (Set.subset_univ _)
  have htail : IntegrableOn f (Set.Icc 0 h)ᶜ volume :=
    hf.mono_set (Set.subset_univ _)
  have heq := setIntegral_union hd measurableSet_Icc.compl hwin htail
  simpa only [Set.union_compl_self] using heq

/-- A positive integrable kernel concentrated in a short positive window
gives the two one-sided bounds needed for the audited abstract squeeze.
The stated numerical mass inequalities are the remaining kernel hypotheses. -/
theorem two_bounds_of_concentrated_kernel
    (k : ℝ → ℝ) (h δ x : ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v) (hki : IntegrableOn k Set.univ volume)
    (hleft : (1 - δ) * Real.exp h ≤ ∫ v : ℝ in Set.Icc 0 h, k v)
    (hright : Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v) ≤ 1 + δ)
    (htail : (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v) ≤ δ) :
    (1 - δ) * logPrimeDensity x ≤ forwardSmooth k x ∧
      backwardSmooth k x ≤ (1 + δ) * logPrimeDensity x + Real.log 4 * δ := by
  have hkiwin : IntegrableOn k (Set.Icc 0 h) volume :=
    hki.mono_set (Set.subset_univ _)
  have hkitail : IntegrableOn k (Set.Icc 0 h)ᶜ volume :=
    hki.mono_set (Set.subset_univ _)
  have hfint : IntegrableOn (fun v : ℝ => k v * logPrimeDensity (x + v))
      Set.univ volume :=
    weighted_density_integrableOn k (fun v : ℝ => x + v) Set.univ hki (by fun_prop)
  have hbint : IntegrableOn (fun v : ℝ => k v * logPrimeDensity (x - v))
      Set.univ volume :=
    weighted_density_integrableOn k (fun v : ℝ => x - v) Set.univ hki (by fun_prop)
  have hfSplit : forwardSmooth k x =
      (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x + v)) +
      (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v * logPrimeDensity (x + v)) := by
    exact integral_split_window _ h hfint
  have hbSplit : backwardSmooth k x =
      (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x - v)) +
      (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v * logPrimeDensity (x - v)) := by
    exact integral_split_window _ h hbint
  have htailnonneg : 0 ≤
      (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v * logPrimeDensity (x + v)) := by
    apply integral_nonneg
    intro v
    exact mul_nonneg (hk v) (logPrimeDensity_nonneg (x + v))
  have hg : 0 ≤ logPrimeDensity x := logPrimeDensity_nonneg x
  have hleft' := mul_le_mul_of_nonneg_right hleft hg
  have hright' := mul_le_mul_of_nonneg_right hright hg
  have hfwindow := future_window_lower_of_integrable k h x hk hkiwin
  have hbwindow := past_window_upper_of_integrable k h x hk hkiwin
  have hbTail := weighted_density_upper_of_integrable k (fun v : ℝ => x - v)
    (Set.Icc 0 h)ᶜ hk hkitail (by fun_prop)
  have hlog : 0 ≤ Real.log 4 := by positivity
  have htail' := mul_le_mul_of_nonneg_left htail hlog
  constructor
  · have hwin_le :
        (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x + v)) ≤
          forwardSmooth k x := by linarith [hfSplit]
    have hmul := mul_le_mul_of_nonneg_left hwin_le (le_of_lt (Real.exp_pos h))
    have hscaled : Real.exp h * ((1 - δ) * logPrimeDensity x) ≤
        Real.exp h * forwardSmooth k x := by nlinarith
    by_contra hnot
    have hlt : forwardSmooth k x < (1 - δ) * logPrimeDensity x :=
      lt_of_not_ge hnot
    have hlt' := mul_lt_mul_of_pos_left hlt (Real.exp_pos h)
    linarith
  · nlinarith [hbSplit]

/-- Conditional prime-density limit: it remains to construct the kernels
and prove their forward/backward averages converge to one. -/
theorem primeDensity_tendsto_of_concentrated_smoothing
    (hkernel : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ (h : ℝ) (k : ℝ → ℝ),
        (∀ v : ℝ, 0 ≤ k v) ∧ IntegrableOn k Set.univ volume ∧
        (1 - δ) * Real.exp h ≤ (∫ v : ℝ in Set.Icc 0 h, k v) ∧
        Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v) ≤ 1 + δ ∧
        (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v) ≤ δ ∧
        Tendsto (forwardSmooth k) atTop (nhds 1) ∧
        Tendsto (backwardSmooth k) atTop (nhds 1)) :
    Tendsto logPrimeDensity atTop (nhds 1) := by
  apply tendsto_one_of_one_sided_smoothing logPrimeDensity (Real.log 4) (by positivity)
  · intro δ hδ hδ1
    obtain ⟨h, k, hk, hki, hl, hr, ht, hf, hb⟩ := hkernel δ hδ hδ1
    refine ⟨forwardSmooth k, hf, ?_⟩
    exact Filter.Eventually.of_forall (fun x =>
      (two_bounds_of_concentrated_kernel k h δ x hk hki hl hr ht).1)
  · intro δ hδ hδ1
    obtain ⟨h, k, hk, hki, hl, hr, ht, hf, hb⟩ := hkernel δ hδ hδ1
    refine ⟨backwardSmooth k, hb, ?_⟩
    exact Filter.Eventually.of_forall (fun x =>
      (two_bounds_of_concentrated_kernel k h δ x hk hki hl hr ht).2)

end HVRPrimeDensityConcentratedSqueeze
