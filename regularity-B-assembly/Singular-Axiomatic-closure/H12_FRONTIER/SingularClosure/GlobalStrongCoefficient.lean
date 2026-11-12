import SingularClosure.GlobalSobolevTrace
import SingularClosure.CanonicalRhsSobolev
import SingularClosure.StrongCoefficientAssembly

/-!
# Global strong coefficient existence under the original AX6 admission

The state, higher-order representative and actual Bochner derivative are
constructed from the canonical Galerkin sequence. No compactness, membership,
initial-trace or equation certificate is an additional premise. Identification
with the literal physical convection remains a separate theorem.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Interval

namespace SingularClosure

noncomputable section

theorem AX6_GLOBAL_STRONG_COEFFICIENT_EXISTS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    Nonempty (GlobalStrongCoefficientNSE ν a ha) := by
  obtain ⟨U, φ, hφ, hc, hi, hconv, hinit, hconstraints⟩ :=
    AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_TRACE hAX6 ν hν a ha
  have hconv0 : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      (U 0) atTop (Icc (0 : ℝ) T) := fun T _ => hconv T 0
  let R := canonicalLimitRhsSobolev hAX6 ν hν a ha (U 0) φ hφ hconv0
  have hRc : ContinuousOn (R 0) (Ici 0) :=
    canonicalLimitRhsSobolev_continuousOn hAX6 ν hν a ha
      (U 0) φ hφ hconv0 (hc 0) 0
  apply NONEMPTY_GLOBAL_STRONG_COEFFICIENT_NSE_OF_CONTINUOUS ν a ha
    (U 1) (U 2) (R 0) (hc 1) (hc 2) hRc (hinit 1) (hi 1)
  · intro t ht
    rw [hi 0 t ht, hi 0 0 le_rfl]
    exact canonicalLimitRhsSobolev_time_integral hAX6 ν hν a ha
      (U 0) φ hφ hconv0 (hc 0) t ht
  · intro t ht k i
    rw [hi 0 t ht]
    exact congrArg (fun c : FourierCoeff => c k i)
      (canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha (U 0) φ hφ hconv0 0 t ht)
  · exact fun t ht => (hconstraints 1 t ht).1
  · exact fun t ht => (hconstraints 1 t ht).2.1
  · exact fun t ht => (hconstraints 1 t ht).2.2

end

end SingularClosure
