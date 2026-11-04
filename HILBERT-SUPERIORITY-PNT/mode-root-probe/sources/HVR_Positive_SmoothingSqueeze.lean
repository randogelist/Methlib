import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

noncomputable section
open Filter

/-!
Generic one-sided smoothing squeeze for the prime-only PNT route.
The eventual inequalities and convergence of the smoothed functions remain
explicit hypotheses. No convolution identity, Fourier theorem or PNT is
asserted here. No local Lean run was performed.
-/
namespace HVRPositiveSmoothingSqueeze

/-- A single one-sided smoothing bound gives an eventual numerical bound. -/
theorem eventually_lt_four_of_upper_smoothing
    (g u : ℝ → ℝ) (hu : Tendsto u atTop (nhds 1))
    (hupper : ∀ᶠ x in atTop, (1 / 2 : ℝ) * g x ≤ u x) :
    ∀ᶠ x in atTop, g x < 4 := by
  have hu2 : ∀ᶠ x in atTop, u x < 2 :=
    (tendsto_order.mp hu).2 2 (by norm_num)
  filter_upwards [hupper, hu2] with x hbound htwo
  linarith

/-- The two one-sided bounds from normalized positive kernels force the
unsmoothed function to tend to one. The term `M * δ` is the explicitly
controlled tail contribution; neither the bounds nor the smoothed limits
are proved by this theorem. -/
theorem tendsto_one_of_one_sided_smoothing
    (g : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hupper : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ u : ℝ → ℝ, Tendsto u atTop (nhds 1) ∧
        ∀ᶠ x in atTop, (1 - δ) * g x ≤ u x)
    (hlower : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ l : ℝ → ℝ, Tendsto l atTop (nhds 1) ∧
        ∀ᶠ x in atTop, l x ≤ (1 + δ) * g x + M * δ) :
    Tendsto g atTop (nhds 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let K : ℝ := |a| + M + 1
    have hK : 0 < K := by dsimp [K]; positivity
    let δ : ℝ := min ((1 - a) / (2 * K)) (1 / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (div_pos (by linarith) (by positivity)) (by norm_num)
    have hδlt : δ < 1 := by
      have h := min_le_right ((1 - a) / (2 * K)) (1 / 2 : ℝ)
      dsimp [δ]
      linarith
    have hδsmall : δ ≤ (1 - a) / (2 * K) := by
      dsimp [δ]
      exact min_le_left _ _
    have hδK : δ * K ≤ (1 - a) / 2 := by
      have h := mul_le_mul_of_nonneg_right hδsmall (le_of_lt hK)
      have heq : ((1 - a) / (2 * K)) * K = (1 - a) / 2 := by
        field_simp [ne_of_gt hK] <;> ring
      linarith
    have hδa : δ * a ≤ δ * |a| :=
      mul_le_mul_of_nonneg_left (le_abs_self a) (le_of_lt hδpos)
    have hthreshold : a * (1 + δ) + M * δ < 1 := by
      dsimp [K] at hδK
      nlinarith
    obtain ⟨l, hl, hbound⟩ := hlower δ hδpos hδlt
    have hlim : ∀ᶠ x in atTop, a * (1 + δ) + M * δ < l x :=
      (tendsto_order.mp hl).1 _ hthreshold
    filter_upwards [hbound, hlim] with x hboundx hlimx
    by_contra hnot
    have hag : g x ≤ a := le_of_not_gt hnot
    have hpos : 0 ≤ 1 + δ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hag hpos
    nlinarith
  · intro b hb
    have hbpos : 0 < b := by linarith
    let δ : ℝ := min ((b - 1) / (2 * b)) (1 / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (div_pos (by linarith) (by positivity)) (by norm_num)
    have hδlt : δ < 1 := by
      have h := min_le_right ((b - 1) / (2 * b)) (1 / 2 : ℝ)
      dsimp [δ]
      linarith
    have hδsmall : δ ≤ (b - 1) / (2 * b) := by
      dsimp [δ]
      exact min_le_left _ _
    have hδb : δ * b ≤ (b - 1) / 2 := by
      have h := mul_le_mul_of_nonneg_right hδsmall (le_of_lt hbpos)
      have heq : ((b - 1) / (2 * b)) * b = (b - 1) / 2 := by
        field_simp [ne_of_gt hbpos] <;> ring
      linarith
    have hthreshold : 1 < (1 - δ) * b := by nlinarith
    obtain ⟨u, hu, hbound⟩ := hupper δ hδpos hδlt
    have hlim : ∀ᶠ x in atTop, u x < (1 - δ) * b :=
      (tendsto_order.mp hu).2 _ hthreshold
    filter_upwards [hbound, hlim] with x hboundx hlimx
    by_contra hnot
    have hbg : b ≤ g x := le_of_not_gt hnot
    have hpos : 0 ≤ 1 - δ := by linarith
    have hmul := mul_le_mul_of_nonneg_left hbg hpos
    linarith

end HVRPositiveSmoothingSqueeze
