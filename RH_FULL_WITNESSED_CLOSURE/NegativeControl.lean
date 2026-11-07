import Architecture

set_option autoImplicit false

namespace RHFullWitnessedClosure.NegativeControl

open RHFullWitnessedClosure

def zeroRat : ExactRat where
  numerator := 0
  denominator := 1

def wrongPacket : RawCert where
  spectralCutoff := 6
  etaSplit := zeroRat
  nearCert := { splitPoint := zeroRat, proofData := [] }
  cells := []
  tailCert := { cutoff := 0, proofData := [] }

def negativeCheckRaw (w : RawCert) : Bool :=
  decide (w.spectralCutoff = 7)

#eval negativeCheckRaw wrongPacket

theorem wrong_packet_rejected :
    negativeCheckRaw wrongPacket = false := by
  decide

#check wrong_packet_rejected
#print axioms RHFullWitnessedClosure.NegativeControl.wrong_packet_rejected

end RHFullWitnessedClosure.NegativeControl
