import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Scoped reconstruction of the real logarithm growth bound needed for the
actual von Mangoldt L-series. The proof follows the argument for
`Real.log_le_rpow_div` in Mathlib, revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0, file
`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`.
Copyright (c) 2018 Chris Hughes. Released under Apache License 2.0.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne,
Sébastien Gouëzel, Rémy Degenne, David Loeffler.

The source directly avoids the specialized and general Mathlib endpoint names
`Real.log_natCast_le_rpow_div` and `Real.log_le_rpow_div`. It retains the real
logarithm, real powers, and the inequality `Real.log_le_sub_one_of_pos`.
Compilation, named axiom audit and dependency diagnostics are pending an
external cached Lean run; no transitive independence is claimed.
-/

noncomputable section

namespace HVRNativeLogRpow

/-- Positive powers dominate the logarithm on the nonnegative real axis. -/
theorem log_le_rpow_div_nonneg {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    Real.log x ≤ x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | hxpos
  · rw [Real.log_zero, Real.zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
  exact (Real.log_rpow hxpos ε).symm.trans_le <|
    (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos ε)).trans
      (sub_one_lt _).le

/-- Exact natural-cast specialization required by HVR summability. -/
theorem log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε :=
  log_le_rpow_div_nonneg (Nat.cast_nonneg n) hε

end HVRNativeLogRpow
