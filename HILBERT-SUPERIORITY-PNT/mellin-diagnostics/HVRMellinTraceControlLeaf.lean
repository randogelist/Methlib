import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
Positive trace control only. This file intentionally uses the selected Mathlib
endpoint. Neither this file nor its bridge should be imported by the PNT proof.
-/

noncomputable section
open Finset Filter MeasureTheory Topology Complex Asymptotics
open scoped BigOperators Topology

namespace HVRMellinTraceControlLeaf

theorem direct_target (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k)
      =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  exact LSeries_eq_mul_integral f hr hs hS hO

end HVRMellinTraceControlLeaf
