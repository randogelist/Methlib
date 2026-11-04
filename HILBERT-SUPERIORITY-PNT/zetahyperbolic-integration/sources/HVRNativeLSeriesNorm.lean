import Mathlib.NumberTheory.LSeries.Basic

/-!
Reconstruct the norm of an L-series term by cases from its definition.
This candidate retains Mathlib's complex-power norm theorem and ordinary
norm/division theory; it does not directly invoke `LSeries.norm_term_eq`.
It must be externally compiled and audited, and a dependency diagnostic is
needed before making claims about transitive uses of the targeted declaration.

The proof is adapted from Mathlib's `Mathlib/NumberTheory/LSeries/Basic.lean`,
Copyright (c) 2021 Aaron Anderson, authors Aaron Anderson and Michael Stoll,
released under the Apache License 2.0.
-/

noncomputable section

namespace HVRNativeLSeriesNorm

/-- A direct norm identity for the actual Mathlib L-series terms, including
the zero-index convention. -/
theorem norm_term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ‖LSeries.term f s n‖ = if n = 0 then 0 else ‖f n‖ / (n : ℝ) ^ s.re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term, if_pos, norm_zero]
  · simp [LSeries.term, hn, Complex.norm_natCast_cpow_of_pos <| Nat.pos_of_ne_zero hn]

end HVRNativeLSeriesNorm
