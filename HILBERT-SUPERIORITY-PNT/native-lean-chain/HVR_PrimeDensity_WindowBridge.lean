import HVR_PrimeDensity_WindowBounds
import HVR_PrimeDensity_WeightedIntegrability

noncomputable section
open MeasureTheory
open HVRPrimeLogDensity HVRPrimeDensityWindowBounds HVRPrimeDensityWeightedIntegrability

/-! Candidate wrappers discharging the shifted-density integrability inputs
from kernel integrability. Kernel construction and smoothing limits are not
proved here. No local Lean run was performed. -/
namespace HVRPrimeDensityWindowBridge

theorem future_window_lower_of_integrable (k : ℝ → ℝ) (h x : ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v) (hki : IntegrableOn k (Set.Icc 0 h) volume) :
    logPrimeDensity x * (∫ v : ℝ in Set.Icc 0 h, k v) ≤
      Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x + v)) := by
  apply future_window_lower k h x hk hki
  exact weighted_density_integrableOn k (fun v : ℝ => x + v) (Set.Icc 0 h)
    hki (by fun_prop)

theorem past_window_upper_of_integrable (k : ℝ → ℝ) (h x : ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v) (hki : IntegrableOn k (Set.Icc 0 h) volume) :
    (∫ v : ℝ in Set.Icc 0 h, k v * logPrimeDensity (x - v)) ≤
      (Real.exp h * logPrimeDensity x) * (∫ v : ℝ in Set.Icc 0 h, k v) := by
  apply past_window_upper k h x hk hki
  exact weighted_density_integrableOn k (fun v : ℝ => x - v) (Set.Icc 0 h)
    hki (by fun_prop)

theorem weighted_density_upper_of_integrable (k q : ℝ → ℝ) (S : Set ℝ)
    (hk : ∀ v : ℝ, 0 ≤ k v) (hki : IntegrableOn k S volume)
    (hq : Measurable q) :
    (∫ v : ℝ in S, k v * logPrimeDensity (q v)) ≤
      Real.log 4 * (∫ v : ℝ in S, k v) :=
  weighted_density_upper k q S hk hki (weighted_density_integrableOn k q S hki hq)

end HVRPrimeDensityWindowBridge
