import SingularClosure.FourierSobolevRhs
import SingularClosure.GlobalSobolevTrace
import SingularClosure.CanonicalRhsSobolev
import SingularClosure.SobolevScaleTimeSmooth

/-!
# All time derivatives of the actual global Galerkin limit

The literal Hilbert-valued derivative constructed from the canonical sequence
equals the smooth Fourier vector field by coefficient injectivity. The proved
Sobolev-scale induction consequently applies to the actual global curves.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff

namespace SingularClosure

noncomputable section

theorem globalSobolevCurves_lower_H0_eq
    (U : ∀ r : ℕ, ℝ → TorusSobolev r)
    (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      torusSobolevInclusion r (U (r + 1) t) = U r t)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    torusSobolevLower 0 r (Nat.zero_le _) (U r t) = U 0 t := by
  apply Subtype.ext
  rw [torusSobolevLower_coeff]
  exact globalSobolevCurves_coeff_eq_H0 U hinclusion r t ht

section Canonical

variable (hAX6 : AX6Statement) (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
variable (U : ∀ r : ℕ, ℝ → TorusSobolev r) (φ : ℕ → ℕ) (hφ : StrictMono φ)
variable (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
  torusSobolevInclusion r (U (r + 1) t) = U r t)
variable (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
  (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
  (U 0) atTop (Icc (0 : ℝ) T))

theorem canonicalLimitRhsSobolev_eq_fourierSobolevRhs
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    canonicalLimitRhsSobolev hAX6 ν hν a ha (U 0) φ hφ hconv r t =
      fourierSobolevRhs ν r (U (r + 2) t) := by
  apply Subtype.ext
  rw [canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha (U 0) φ hφ hconv r t ht,
    fourierSobolevRhs_coefficient_eq_fullRhs,
    globalSobolevCurves_lower_H0_eq U hinclusion (r + 2) t ht]

theorem canonicalGlobalSobolevCurves_hasDerivWithinAt
    (hcontinuous : ContinuousOn (U 0) (Ici 0))
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (U r) (fourierSobolevRhs ν r (U (r + 2) t)) (Ici 0) t := by
  have hd := canonicalLimitRhsSobolev_hasDerivWithinAt_order hAX6 ν hν a ha
    (U 0) φ hφ hconv hcontinuous r (U r)
    (fun t ht => globalSobolevCurves_coeff_eq_H0 U hinclusion r t ht) t ht
  rwa [canonicalLimitRhsSobolev_eq_fourierSobolevRhs
    hAX6 ν hν a ha U φ hφ hinclusion hconv r t ht] at hd

/-- Actual canonical convergence and the actual derivative equation discharge
every input of the Sobolev-scale time-regularity induction. -/
theorem canonicalGlobalSobolevCurves_time_smooth
    (hcontinuous : ∀ r, ContinuousOn (U r) (Ici 0)) :
    ∀ r, ContDiffOn ℝ ∞ (U r) (Ici 0) := by
  apply SOBOLEV_SCALE_TIME_SMOOTH U (fourierSobolevRhs ν) hcontinuous
    (fourierSobolevRhs_contDiff ν)
  intro r t ht
  exact canonicalGlobalSobolevCurves_hasDerivWithinAt hAX6 ν hν a ha U φ hφ
    hinclusion hconv (hcontinuous 0) r t ht

end Canonical

/-- Under AX6 the actual common Galerkin limit has every time derivative in
every Sobolev space, including the initial-time boundary. -/
theorem AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_SMOOTH (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ U : ∀ r : ℕ, ℝ → TorusSobolev r, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ r, ContDiffOn ℝ ∞ (U r) (Ici 0)) ∧
      (∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        torusSobolevInclusion r (U (r + 1) t) = U r t) ∧
      (∀ (T : ℝ) (r : ℕ), TendstoUniformlyOn
        (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t)
        (U r) atTop (Icc (0 : ℝ) T)) ∧
      (∀ r, U r 0 = smoothDatumSobolev r a ha.smooth ha.periodic) ∧
      (∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        SpectralReality (U r t).val ∧ SpectralSolenoidal (U r t).val ∧
          SpectralMeanZero (U r t).val) ∧
      ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        HasDerivWithinAt (U r) (fourierSobolevRhs ν r (U (r + 2) t)) (Ici 0) t := by
  obtain ⟨U, φ, hφ, hcontinuous, hinclusion, hconv, hinit, hconstraints⟩ :=
    AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_TRACE hAX6 ν hν a ha
  have hconv0 : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      (U 0) atTop (Icc (0 : ℝ) T) := fun T _ => hconv T 0
  exact ⟨U, φ, hφ,
    canonicalGlobalSobolevCurves_time_smooth hAX6 ν hν a ha U φ hφ
      hinclusion hconv0 hcontinuous,
    hinclusion, hconv, hinit, hconstraints,
    canonicalGlobalSobolevCurves_hasDerivWithinAt hAX6 ν hν a ha U φ hφ
      hinclusion hconv0 (hcontinuous 0)⟩

end

end SingularClosure
