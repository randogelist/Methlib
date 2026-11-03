import HVRMellinTraceControlLeaf

/-!
Two-hop positive trace control. This file intentionally depends on the selected
Mathlib endpoint through HVRMellinTraceControlLeaf.direct_target.
-/

noncomputable section
open Finset Filter Asymptotics
open scoped BigOperators Topology

namespace HVRMellinTraceControlBridge

theorem indirect_target (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k)
      =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  exact HVRMellinTraceControlLeaf.direct_target f hr hs hS hO

end HVRMellinTraceControlBridge
