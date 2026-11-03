import HVR_PrimeLogDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory
open HVRPrimeLogDensity

/-! Candidate integral estimates for the actual prime density. Kernels and
integrability hypotheses are explicit. These are finite-window/tail bounds;
no existence of band-limited kernels, Fourier limit or PNT is asserted.
The statements await the user's external Lean build and theorem-level audit.
-/
namespace HVRPrimeDensityWindowBounds

/-- A future window controls the density at its left endpoint. -/
theorem future_window_lower (k : ℝ → ℝ) (h x : ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v)
    (hki : IntegrableOn k (Set.Icc 0 h) volume)
    (hfi : IntegrableOn (fun v : ℝ => k v * logPrimeDensity (x + v))
      (Set.Icc 0 h) volume) :
    logPrimeDensity x * (∫ v : ℝ in Set.Icc 0 h, k v) ≤
      Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x + v)) := by
  have hcmp :
      (∫ v : ℝ in Set.Icc 0 h, logPrimeDensity x * k v) ≤
        (∫ v : ℝ in Set.Icc 0 h, Real.exp h * (k v * logPrimeDensity (x + v))) := by
    apply integral_mono_ae (hki.const_mul (logPrimeDensity x)) (hfi.const_mul (Real.exp h))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hexp : Real.exp v ≤ Real.exp h := Real.exp_le_exp.mpr hv.2
    have hstep : Real.exp v * logPrimeDensity (x + v) ≤
        Real.exp h * logPrimeDensity (x + v) :=
      mul_le_mul_of_nonneg_right hexp (logPrimeDensity_nonneg (x + v))
    have hpoint : logPrimeDensity x ≤ Real.exp h * logPrimeDensity (x + v) :=
      le_trans (logPrimeDensity_le_future x v hv.1) hstep
    have hweighted := mul_le_mul_of_nonneg_left hpoint (hk v)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hweighted
  simpa only [integral_const_mul] using hcmp

/-- A past window is controlled by the density at its right endpoint. -/
theorem past_window_upper (k : ℝ → ℝ) (h x : ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v)
    (hki : IntegrableOn k (Set.Icc 0 h) volume)
    (hpi : IntegrableOn (fun v : ℝ => k v * logPrimeDensity (x - v))
      (Set.Icc 0 h) volume) :
    (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x - v)) ≤
      (Real.exp h * logPrimeDensity x) * (∫ v : ℝ in Set.Icc 0 h, k v) := by
  have hcmp :
      (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x - v)) ≤
        (∫ v : ℝ in Set.Icc 0 h, (Real.exp h * logPrimeDensity x) * k v) := by
    apply integral_mono_ae hpi (hki.const_mul (Real.exp h * logPrimeDensity x))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hexp : Real.exp v ≤ Real.exp h := Real.exp_le_exp.mpr hv.2
    have hstep : Real.exp v * logPrimeDensity x ≤ Real.exp h * logPrimeDensity x :=
      mul_le_mul_of_nonneg_right hexp (logPrimeDensity_nonneg x)
    have hpoint : logPrimeDensity (x - v) ≤ Real.exp h * logPrimeDensity x :=
      le_trans (logPrimeDensity_past_le x v hv.1) hstep
    have hweighted := mul_le_mul_of_nonneg_left hpoint (hk v)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hweighted
  simpa only [integral_const_mul] using hcmp

/-- The uniform Chebyshev bound controls the contribution of any kernel tail.
The domain and shifted argument are arbitrary; all integrability is explicit. -/
theorem weighted_density_upper (k q : ℝ → ℝ) (S : Set ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v)
    (hki : IntegrableOn k S volume)
    (hqi : IntegrableOn (fun v : ℝ => k v * logPrimeDensity (q v)) S volume) :
    (∫ v : ℝ in S, k v * logPrimeDensity (q v)) ≤
      Real.log 4 * (∫ v : ℝ in S, k v) := by
  have hcmp : (∫ v : ℝ in S, k v * logPrimeDensity (q v)) ≤
      (∫ v : ℝ in S, Real.log 4 * k v) := by
    apply integral_mono hqi (hki.const_mul (Real.log 4))
    intro v
    have h := mul_le_mul_of_nonneg_left (logPrimeDensity_le_log_four (q v)) (hk v)
    simpa only [mul_comm] using h
  simpa only [integral_const_mul] using hcmp

end HVRPrimeDensityWindowBounds
