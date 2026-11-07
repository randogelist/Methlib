import Tail16Frontier.DodgsonPruning

-- Finite cell validity is not a proof of the native RH proposition.
example : _root_.RiemannHypothesis := by
  exact RHFinitePruning.Dodgson.positiveControl_valid
