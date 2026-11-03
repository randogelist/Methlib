import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
A restricted, source-level reconstruction of the real-to-complex logarithm
identity from the real and imaginary parts of the principal complex logarithm.
The proof follows the corresponding Mathlib proof in
`Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`:
Copyright (c) 2018 Chris Hughes. Released under Apache License 2.0.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne,
Benjamin Davidson.

This source is an external-build candidate and is not yet compiled or audited.
It retains the norm and argument lemmas used in the proof. In particular,
absence of the original named endpoint in source is not proof of transitive
independence.
-/

noncomputable section

namespace HVRComplexLogNative

/-- The principal complex log agrees with the real log on nonnegative reals. -/
theorem complex_log_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Complex.log (x : ℂ) = (Real.log x : ℂ) := by
  apply Complex.ext
  · rw [Complex.log_re, Complex.norm_of_nonneg hx, Complex.ofReal_re]
  · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx, Complex.ofReal_im]

/-- Natural numbers are a particular nonnegative case. -/
theorem complex_log_nat (n : ℕ) :
    Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
  simpa only [Complex.ofReal_natCast] using
    (complex_log_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n))

end HVRComplexLogNative
