import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Complex.Basic

/-
The scaling proof adapts Mathlib/Topology/Algebra/InfiniteSum/Ring.lean,
copyright 2017 Johannes Hölzl, Apache License 2.0.
-/

/-!
Scoped series-interface replacements for the HVR prime-power argument.

These proofs adapt the standard Mathlib definitions and arguments; they use
general Mathlib map/continuity, summability uniqueness, and the norm-majorant
comparison theorem. Avoiding selected theorem names is not a claim of
independence from the general summability theory, nor of transitive dependency
independence. This source has not been compiled or audited yet.
-/

noncomputable section

namespace HVRNativeSeriesInfrastructure

/-- Scale a complex series using a continuous additive map. -/
theorem hasSum_scale {f : ℕ → ℂ} {a : ℂ} (h : HasSum f a) (c : ℂ) :
    HasSum (fun n => c * f n) (c * a) := by
  simpa only using! h.map (AddMonoidHom.mulLeft c) (continuous_const.mul continuous_id)

/-- Identify the totalized sum by existence and uniqueness of the limit. -/
theorem hasSum_identifies_tsum {f : ℕ → ℂ} {a : ℂ} (h : HasSum f a) :
    (∑' n, f n) = a := by
  exact h.summable.hasSum.unique h

/-- Direct comparison for the complex series and real majorant used in HVR. -/
theorem complex_summable_of_majorant {f : ℕ → ℂ} {g : ℕ → ℝ}
    (hg : Summable g) (h : ∀ n, ‖f n‖ ≤ g n) : Summable f := by
  exact hg.of_norm_bounded h

end HVRNativeSeriesInfrastructure
