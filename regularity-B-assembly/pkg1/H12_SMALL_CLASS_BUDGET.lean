import H12_SIGMA_ZERO_SMALL_CLASS
import H12_CRITICAL_ENERGY_BUDGET

/-!
# Concrete small critical data and a uniform scalar energy budget

Membership in the concrete Fourier class supplies positivity and initial
critical smallness.  The trajectory variables in this file remain scalar
functions: continuity, nonnegativity, the differential energy law, the
initial-energy comparison, and interpolation are explicit hypotheses.
No identification with actual NSE/Galerkin trajectories is asserted.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace H12SmallClassBudget

open H12SigmaZeroSmallClass H12CriticalEnergyBudget

/-- The class radius `ν/(8 C3³)` supplies the quarter-viscosity margin
required by the scalar critical-energy theorem. -/
theorem small_critical_coefficient_le
    {ν C3 : ℝ} {a : RealH12Datum} (ha : Small ν C3 a) :
    C3 ^ 3 * Real.sqrt (criticalSq a) ≤ (1 / 4 : ℝ) * ν := by
  have hn := small_norm_lt ha
  change Real.sqrt (criticalSq a) < ν / (8 * C3 ^ 3) at hn
  have hden : 0 < 8 * C3 ^ 3 := by
    have hC3 := ha.2.1
    positivity
  have hmul := (lt_div_iff₀ hden).mp hn
  have hν := ha.1
  nlinarith

/-- Concrete small-class admission compiles to a uniform square-enstrophy
budget for every scalar family satisfying the displayed energy laws.
Smallness and its persistence are not supplied as additional hypotheses. -/
theorem H12_SMALL_CLASS_UNIFORM_SQUARE_ENSTROPHY
    {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C3 T : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (hT : 0 ≤ T)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ criticalSq a)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C3 ^ 3 * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t) :
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      criticalSq a ^ 2 / (2 * (1 - (1 / 4 : ℝ)) * ν) := by
  exact H12_UNIFORM_SQUARE_ENSTROPHY_OF_SMALL_DATA
    ha.1 (pow_pos ha.2.1 3) (by norm_num) hT (criticalSq_nonneg a)
    hH hD hE hH_nonneg hD_nonneg hderiv h_initial
    (small_critical_coefficient_le ha) hcritical hinterpolation

/-- A common finite real budget is constructed explicitly from the
datum; no existence of a budget is an input to this theorem. -/
theorem H12_SMALL_CLASS_EXISTS_UNIFORM_BUDGET
    {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C3 T : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (hT : 0 ≤ T)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ criticalSq a)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C3 ^ 3 * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤ M := by
  refine ⟨criticalSq a ^ 2 / (2 * (1 - (1 / 4 : ℝ)) * ν), ?_, ?_⟩
  · have hν := ha.1
    positivity
  · exact H12_SMALL_CLASS_UNIFORM_SQUARE_ENSTROPHY a ha hT
      hH hD hE hH_nonneg hD_nonneg hderiv h_initial hcritical hinterpolation

end H12SmallClassBudget
