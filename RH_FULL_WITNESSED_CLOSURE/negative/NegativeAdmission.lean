import NegativeControl

namespace RHFullWitnessedClosure.NegativeControl

/-- This theorem is deliberately false and must fail with `decide`. -/
theorem wrong_packet_false_admission :
    negativeCheckRaw wrongPacket = true := by
  decide

end RHFullWitnessedClosure.NegativeControl
