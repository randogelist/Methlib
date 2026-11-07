import CoordinateData
import RH_HilbertLimit.AnalyticClosure
import Mathlib.Analysis.Calculus.Deriv.Basic
import Std

/-!
# Finite witness admission architecture for actual xi

The checker is executable and finite.  Its soundness field must prove the
exact actual-xi separation theorem.  The exit theorem is the existing
Mathlib-backed endpoint
`RH_HilbertLimit.canonical_actual_all_variation_one_iff_nativeRH`.

No witness, checker soundness proof, or analytic premise is asserted here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RHFullWitnessedClosure

def heatRate (ν : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * ν

def actualDelta (N : ℕ) : ℝ :=
  RH_HilbertLimit.actualVariation (N + 1) -
    RH_HilbertLimit.actualVariation N

def actualEnergy (ν η : ℝ) : ℝ :=
  Real.exp (-(heatRate ν * η)) +
    ∑' N : ℕ,
      actualDelta N *
        Real.exp (-(heatRate ν * (((N : ℝ) + 2) ^ 2) * η))

def actualB0 (ν η : ℝ) : ℝ :=
  1 + actualEnergy ν η

def actualB1 (ν η : ℝ) : ℝ :=
  -deriv (actualEnergy ν) η

def actualB2 (ν η : ℝ) : ℝ :=
  deriv (deriv (actualEnergy ν)) η

def actualB3 (ν η : ℝ) : ℝ :=
  -deriv (deriv (deriv (actualEnergy ν))) η

def actualG2 (ν η : ℝ) : ℝ :=
  actualB0 ν η * actualB2 ν η -
    2 * actualB1 ν η ^ 2

def actualG3 (ν η : ℝ) : ℝ :=
  actualB0 ν η * actualB3 ν η -
    3 * actualB1 ν η * actualB2 ν η

def verifiedHeight : ℝ :=
  3 * 10 ^ 12

def verifiedRate : ℝ :=
  2 ^ 25 / (3 * verifiedHeight ^ 4)

def actualEtaStar (ν : ℝ) : ℝ :=
  100 * verifiedRate ^ 2 / heatRate ν

def ActualSeparation (ν : ℝ) : Prop :=
  ∀ η : ℝ,
    0 < η →
    η < actualEtaStar ν →
    actualG2 ν η = 0 →
    0 < actualG3 ν η

def ActualDerivativeIdentity (ν : ℝ) : Prop :=
  ∀ η : ℝ,
    0 < η →
    η < actualEtaStar ν →
    HasDerivAt (actualG2 ν) (-actualG3 ν η) η

def ActualPositivity (ν : ℝ) : Prop :=
  ∀ η : ℝ,
    0 < η →
    η ≤ actualEtaStar ν →
    0 ≤ actualG2 ν η

structure NativeAnalyticPremises (ν : ℝ) where
  nu_pos : 0 < ν
  cutoff : 0 < actualG2 ν (actualEtaStar ν)
  derivativeIdentity : ActualDerivativeIdentity ν
  propagate :
    (0 < actualG2 ν (actualEtaStar ν)) →
    ActualDerivativeIdentity ν →
    ActualSeparation ν →
    ActualPositivity ν
  positivityToAllVariationOne :
    ActualPositivity ν →
    ∀ N : ℕ, RH_HilbertLimit.actualVariation N = 1

structure CoordinateKernel (ν : ℝ) where
  decodeBlob : ByteArray → Option RawCert
  checkRaw : RawCert → Bool
  checkRaw_sound :
    ∀ w : RawCert,
      checkRaw w = true →
      ActualSeparation ν

def verifyBlob {ν : ℝ} (K : CoordinateKernel ν) (blob : ByteArray) : Bool :=
  match K.decodeBlob blob with
  | none => false
  | some w => K.checkRaw w

theorem verifyBlob_sound
    {ν : ℝ}
    (K : CoordinateKernel ν)
    (blob : ByteArray)
    (hAccepted : verifyBlob K blob = true) :
    ActualSeparation ν := by
  cases hDecode : K.decodeBlob blob with
  | none =>
      simp [verifyBlob, hDecode] at hAccepted
  | some w =>
      have hRaw : K.checkRaw w = true := by
        simpa [verifyBlob, hDecode] using hAccepted
      exact K.checkRaw_sound w hRaw

structure ClosedSystem where
  ν : ℝ
  premises : NativeAnalyticPremises ν
  kernel : CoordinateKernel ν

theorem verified_blob_implies_nativeRH
    (S : ClosedSystem)
    (blob : ByteArray)
    (hAccepted : verifyBlob S.kernel blob = true) :
    _root_.RiemannHypothesis := by
  have hSep : ActualSeparation S.ν :=
    verifyBlob_sound S.kernel blob hAccepted
  have hPos : ActualPositivity S.ν :=
    S.premises.propagate
      S.premises.cutoff
      S.premises.derivativeIdentity
      hSep
  have hAll : ∀ N : ℕ, RH_HilbertLimit.actualVariation N = 1 :=
    S.premises.positivityToAllVariationOne hPos
  exact
    (RH_HilbertLimit.canonical_actual_all_variation_one_iff_nativeRH).mp hAll

theorem exists_verified_blob_implies_nativeRH
    (S : ClosedSystem)
    (hExists : ∃ blob : ByteArray, verifyBlob S.kernel blob = true) :
    _root_.RiemannHypothesis := by
  rcases hExists with ⟨blob, hAccepted⟩
  exact verified_blob_implies_nativeRH S blob hAccepted

#check RH_HilbertLimit.canonical_actual_all_variation_one_iff_nativeRH
#check verifyBlob_sound
#check verified_blob_implies_nativeRH
#check exists_verified_blob_implies_nativeRH

#print axioms RHFullWitnessedClosure.verifyBlob_sound
#print axioms RHFullWitnessedClosure.verified_blob_implies_nativeRH
#print axioms RHFullWitnessedClosure.exists_verified_blob_implies_nativeRH

end RHFullWitnessedClosure
