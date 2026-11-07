import Tail16Frontier.DodgsonPruning

-- Supplying finite cells does not supply the accepted-witness necessity proof.
def missingBridge :
    RHFrozenWitness.TailKernel.CertifiedDodgsonProjection
      Tail16Frontier.fixedPrimitiveKernel where
  cells := fun _ => [RHFinitePruning.Dodgson.negativeControl]
