import Mathlib.Analysis.Complex.Trigonometric

/-!
An HVR-scoped reconstruction of the norm of the complex exponential.
The derivation adapts Mathlib's `Complex.norm_exp` proof in
`Mathlib/Analysis/Complex/Trigonometric.lean` at revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0:
Copyright (c) 2018 Chris Hughes. Released under Apache License 2.0.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir.

This source candidate has not been externally compiled or audited. It uses
the complex exponential factorization and unit-circle norm, and does not
directly invoke the named `Complex.norm_exp` theorem. Transitive dependency
diagnostics remain necessary.
-/

noncomputable section

namespace HVRComplexNormExpNative

/-- The norm of the complex exponential is the real exponential of the real part. -/
theorem norm_exp_rebuild (z : ℂ) : ‖Complex.exp z‖ = Real.exp z.re := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos, Complex.norm_mul,
    Complex.norm_exp_ofReal, Complex.norm_cos_add_sin_mul_I, mul_one]

end HVRComplexNormExpNative
