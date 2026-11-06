import HXYThreeSpaces.Main

/-! Public root: the exact frozen conjunction of the H_XY and three RH equivalences. -/

theorem HXY_THREE_FUNCTION_SPACE_EQUIVALENCES :
    (∀ X Y : ℕ, HXYThreeSpaces.HXY X Y ↔ _root_.RiemannHypothesis) ∧
    (_root_.RiemannHypothesis ↔ HXYThreeSpaces.BanachExt) ∧
    (_root_.RiemannHypothesis ↔ HXYThreeSpaces.HilbertRep) ∧
    (_root_.RiemannHypothesis ↔ HXYThreeSpaces.HolExt) :=
  HXYThreeSpaces.frozen_three_equivalences
