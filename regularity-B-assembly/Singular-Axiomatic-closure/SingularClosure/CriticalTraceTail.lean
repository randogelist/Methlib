import SingularClosure.CriticalSpacesCutoff
import SingularClosure.CriticalTrace

/-!
# Same-order L2 decay of Fourier projection tails

Strong convergence of the actual coefficient cutoffs is lifted to time L2
by dominated convergence. No uniform-in-time tail decay is assumed here.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace SingularClosure

noncomputable section

theorem criticalTrace_integrable_norm_sq
    {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    {μ : Measure α} {u : α → H} (hu : MemLp u 2 μ) :
    Integrable (fun t => ‖u t‖ ^ 2) μ := by
  simpa only [pow_two, Pi.mul_apply] using hu.norm.integrable_mul hu.norm

/-- Every contraction approximating the identity has vanishing time-L2 tails. -/
theorem criticalTrace_L2_projection_tail
    {α H : Type*} [MeasurableSpace α] [NormedAddCommGroup H]
    [NormedSpace ℂ H] {μ : Measure α}
    (P : ℕ → H →L[ℂ] H)
    (hP : ∀ N x, ‖P N x‖ ≤ ‖x‖)
    (hlim : ∀ x : H, Tendsto (fun N => P N x) atTop (𝓝 x))
    (u : α → H) (hu : MemLp u 2 μ) :
    Tendsto (fun N => ∫ t, ‖u t - P N (u t)‖ ^ 2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
  have hmem : ∀ N, MemLp (fun t => u t - P N (u t)) 2 μ := by
    intro N
    exact hu.sub ((P N).comp_memLp' hu)
  have hbound : ∀ N, ∀ᵐ t ∂μ,
      ‖‖u t - P N (u t)‖ ^ 2‖ ≤ 4 * ‖u t‖ ^ 2 := by
    intro N
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hb : ‖u t - P N (u t)‖ ≤ 2 * ‖u t‖ := by
        calc
          _ ≤ ‖u t‖ + ‖P N (u t)‖ := norm_sub_le _ _
          _ ≤ 2 * ‖u t‖ := by linarith [hP N (u t)]
      nlinarith [norm_nonneg (u t - P N (u t)), norm_nonneg (u t)]
  have hpoint : ∀ᵐ t ∂μ,
      Tendsto (fun N => ‖u t - P N (u t)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    exact Filter.Eventually.of_forall fun t => by
      have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => u t) atTop (𝓝 (u t))).sub
        (hlim (u t))).norm.pow 2
      simpa using ht
  have h := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun N t => ‖u t - P N (u t)‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun t => 4 * ‖u t‖ ^ 2)
    (fun N => (hmem N).aestronglyMeasurable.norm.pow 2)
    ((criticalTrace_integrable_norm_sq hu).const_mul 4) hbound hpoint
  simpa only [integral_zero] using h

/-- Same-order Fourier tails vanish in the actual Bochner time-L2 norm. -/
theorem CRITICAL_SOBOLEV_CUTOFF_L2_TAIL
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (q : ℤ) (u : α → CriticalSobolev q) (hu : MemLp u 2 μ) :
    Tendsto (fun N => ∫ t, ‖u t - criticalSobolevCutoff q N (u t)‖ ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) :=
  criticalTrace_L2_projection_tail (criticalSobolevCutoff q)
    (criticalSobolevCutoff_norm_le q) (criticalSobolevCutoff_tendsto q) u hu

/-- The same result on the literal finite forward time interval. -/
theorem CRITICAL_SOBOLEV_CUTOFF_INTERVAL_L2_TAIL
    (q : ℤ) (u : ℝ → CriticalSobolev q) {T : ℝ} (hT : 0 ≤ T)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T))) :
    Tendsto (fun N => ∫ t in (0 : ℝ)..T,
      ‖u t - criticalSobolevCutoff q N (u t)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  simpa only [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc] using
    CRITICAL_SOBOLEV_CUTOFF_L2_TAIL q u hu

end

end SingularClosure
