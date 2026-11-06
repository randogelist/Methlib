import HXYThreeSpaces.HXY
import HXYThreeSpaces.Banach
import HXYThreeSpaces.Hilbert
import HXYThreeSpaces.Holomorphic

/-!
# Deterministic final composition of the three frozen candidates

The root is an explicit conjunction, not an iterated binary biconditional.
No existence premise is introduced beyond the temporary RH hypothesis in the
conditional construction theorem. Exact native compilation and axiom audit
are required before A-tier promotion.
-/

set_option autoImplicit false
noncomputable section

namespace HXYThreeSpaces

def FrozenEquivalences : Prop :=
  (∀ X Y : ℕ, HXY X Y ↔ _root_.RiemannHypothesis) ∧
  (_root_.RiemannHypothesis ↔ BanachExt) ∧
  (_root_.RiemannHypothesis ↔ HilbertRep) ∧
  (_root_.RiemannHypothesis ↔ HolExt)

theorem frozen_three_equivalences : FrozenEquivalences :=
  ⟨HXY_iff_nativeRH, nativeRH_iff_banachExt,
    nativeRH_iff_hilbertRep, nativeRH_iff_holExt⟩

theorem all_three_of_nativeRH (hRH : _root_.RiemannHypothesis) :
    BanachExt ∧ HilbertRep ∧ HolExt :=
  ⟨banachExt_of_nativeRH hRH, hilbertRep_of_nativeRH hRH, holExt_of_nativeRH hRH⟩

theorem HXY_iff_banachExt (X Y : ℕ) : HXY X Y ↔ BanachExt :=
  (HXY_iff_nativeRH X Y).trans nativeRH_iff_banachExt

theorem HXY_iff_hilbertRep (X Y : ℕ) : HXY X Y ↔ HilbertRep :=
  (HXY_iff_nativeRH X Y).trans nativeRH_iff_hilbertRep

theorem HXY_iff_holExt (X Y : ℕ) : HXY X Y ↔ HolExt :=
  (HXY_iff_nativeRH X Y).trans nativeRH_iff_holExt

theorem all_three_of_HXY (X Y : ℕ) (h : HXY X Y) :
    BanachExt ∧ HilbertRep ∧ HolExt :=
  all_three_of_nativeRH (nativeRH_of_HXY X Y h)

theorem frozen_HXY_equivalences :
    ∀ X Y : ℕ,
      (HXY X Y ↔ _root_.RiemannHypothesis) ∧
      (HXY X Y ↔ BanachExt) ∧
      (HXY X Y ↔ HilbertRep) ∧
      (HXY X Y ↔ HolExt) :=
  fun X Y => ⟨HXY_iff_nativeRH X Y, HXY_iff_banachExt X Y,
    HXY_iff_hilbertRep X Y, HXY_iff_holExt X Y⟩

end HXYThreeSpaces
