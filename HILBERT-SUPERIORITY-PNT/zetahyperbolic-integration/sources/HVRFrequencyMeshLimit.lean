import HVRFrequencyGridWeights
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
Rate-to-limit step for a regular frequency grid.

This candidate converts an explicit O(1/N) norm estimate into convergence.
It does not prove either of the two analytic error estimates for the actual
prime-density integrals. No local Lean compilation or external audit was run.
-/

noncomputable section
open Filter
open scoped Topology

namespace HVRFrequencyMeshLimit

theorem grid_mesh_tendsto_zero (R : ℝ) :
    Tendsto (fun N : ℕ => 2 * R / (N : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat (2 * R)

/-- A quantitative finite-grid error bound supplies its limiting obligation. -/
theorem tendsto_of_grid_error (R C : ℝ) (approx : ℕ → ℂ) (target : ℂ)
    (herror : ∀ N : ℕ, 0 < N →
      ‖approx N - target‖ ≤ (2 * R / (N : ℝ)) * C) :
    Tendsto approx atTop (𝓝 target) := by
  have hscale : Tendsto (fun N : ℕ => (2 * R / (N : ℝ)) * C)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using (grid_mesh_tendsto_zero R).mul_const C
  have heventual : ∀ᶠ N : ℕ in atTop,
      ‖approx N - target‖ ≤ (2 * R / (N : ℝ)) * C := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact herror N hN
  have herr : Tendsto (fun N : ℕ => approx N - target) atTop (𝓝 0) :=
    squeeze_zero_norm' heventual hscale
  have h := herr.add (tendsto_const_nhds (x := target))
  simpa only [zero_add, sub_add_cancel] using h

end HVRFrequencyMeshLimit
