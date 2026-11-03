/- Adapted from the earlier HVR implementation, itself based on Mathlib4
   Mathlib/NumberTheory/LSeries/Dirichlet.lean, Copyright 2024 Michael Stoll,
   Apache License 2.0. See the accompanying Mathlib license. -/
import NextPrimePowerReindex
import NextZetaLogDerivative

/-!
Candidate exact bridge from the prime Euler series to the logarithmic derivative
of actual zeta. This directly composes two source candidates; the proof requires
external compilation, theorem-level axiom audit, and dependency tracing.
-/

noncomputable section

namespace HVRNextEulerPrimeZetaBridge

theorem eulerProductLogDerivative : HVRNativeZetaLogDerivative.EulerProductLogDerivative := by
  intro s hs
  exact (HVRNextPrimePowerReindex.primePowerReindexing s hs).symm.trans
    (HVRNextZetaLogDerivative.vonMangoldt_LSeries_eq_neg_logDeriv_zeta hs)

end HVRNextEulerPrimeZetaBridge
