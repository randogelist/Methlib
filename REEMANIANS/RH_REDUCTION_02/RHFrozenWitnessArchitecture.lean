import RH_HilbertLimit.ActualCancellationWitness

set_option autoImplicit false

namespace RHFrozenWitness

def budget16 (Y : Nat) : RH_HilbertLimit.CancellationBudget :=
  { cutoff := 16, coefficient := Y }

/--
Finite-certificate kernel interface.

`Cert` is the finite witness language.
`check` is the terminating Boolean checker.
`sound` states that checker acceptance proves the fixed actual-ξ
cancellation-budget proposition.  This kernel is implementation
infrastructure; it is not witness data.
-/
structure TailKernel where
  Cert : Type
  coefficient : Cert → Nat
  check : Cert → Bool
  sound :
    ∀ c : Cert,
      check c = true →
      (budget16 (coefficient c)).Admissible

namespace TailKernel

theorem check_sound
    (K : TailKernel)
    (c : K.Cert)
    (h : K.check c = true) :
    _root_.RiemannHypothesis := by
  exact
    RH_HilbertLimit.nativeRH_of_admissible_cancellationBudget
      (budget16 (K.coefficient c))
      (K.sound c h)

structure Decoder (K : TailKernel) where
  decode : ByteArray → Option K.Cert

def verify
    (K : TailKernel)
    (D : Decoder K)
    (blob : ByteArray) : Bool :=
  match D.decode blob with
  | none => false
  | some c => K.check c

theorem verify_sound
    (K : TailKernel)
    (D : Decoder K)
    (blob : ByteArray)
    (h : verify K D blob = true) :
    _root_.RiemannHypothesis := by
  unfold verify at h
  split at h
  · contradiction
  · rename_i c hdec
    exact K.check_sound c h

end TailKernel

theorem exists_checked_implies_nativeRH
    (K : TailKernel)
    (hExists : ∃ c : K.Cert, K.check c = true) :
    _root_.RiemannHypothesis := by
  rcases hExists with ⟨c, hc⟩
  exact K.check_sound c hc

theorem exists_verified_blob_implies_nativeRH
    (K : TailKernel)
    (D : TailKernel.Decoder K)
    (hExists : ∃ blob : ByteArray, TailKernel.verify K D blob = true) :
    _root_.RiemannHypothesis := by
  rcases hExists with ⟨blob, hb⟩
  exact TailKernel.verify_sound K D blob hb

#check RH_HilbertLimit.CancellationBudget
#check RH_HilbertLimit.nativeRH_of_admissible_cancellationBudget
#check TailKernel
#check TailKernel.check_sound
#check TailKernel.Decoder
#check TailKernel.verify
#check TailKernel.verify_sound
#check exists_checked_implies_nativeRH
#check exists_verified_blob_implies_nativeRH

#print axioms RHFrozenWitness.TailKernel.check_sound
#print axioms RHFrozenWitness.TailKernel.verify_sound
#print axioms RHFrozenWitness.exists_checked_implies_nativeRH
#print axioms RHFrozenWitness.exists_verified_blob_implies_nativeRH

end RHFrozenWitness
