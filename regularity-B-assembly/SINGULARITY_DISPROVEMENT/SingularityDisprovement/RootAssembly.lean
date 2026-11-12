import SingularityDisprovement.Scaling

/-! Explicit logical assembly.  The abstract seed theorem records its actual
membership and essential-unboundedness premises; the unconditional root must
instantiate these with the proved dyadic datum. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal

namespace SingularityDisprovement
open SingularClosure
noncomputable section

def Premise (ν ε : ℝ) (a : CriticalSobolev 1) : Prop :=
  CriticalSigmaZero a ∧ 0 < ‖a‖ ∧ ‖a‖ < ε ∧
    calibratedScore ν a < 2 ∧ EssUnbounded a

theorem PREMISE_IMPLIES_REGULARITY (ν ε : ℝ) (hν : 0 < ν)
    (a : CriticalSobolev 1) (ha : Premise ν ε a) : Reg ν a :=
  ADMISSION_IMPLIES_REGULARITY ν hν a ha.1 ha.2.2.2.1

theorem ADMISSION_NONEMPTY_OF_ACTUAL_SEED (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (b : CriticalSobolev 1) (hb : CriticalSigmaZero b)
    (hbpos : 0 < ‖b‖) (hbunbounded : EssUnbounded b) :
    ∃ a : CriticalSobolev 1, Premise ν ε a := by
  obtain ⟨m, hm, hpos, hnorm, hscore⟩ :=
    SMALL_POSITIVE_DYADIC_SCALE_EXISTS ν ε hν hε b hb hbpos
  have hr : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) _
  refine ⟨((1 / 2 : ℝ) ^ m) • b,
    sigma_real_smul _ b hb, hpos, hnorm, ?_, hbunbounded.smul _ hr⟩
  exact hscore.trans (by norm_num)

theorem REGULARITY_CHAIN_OF_ACTUAL_SEED (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (b : CriticalSobolev 1) (hb : CriticalSigmaZero b)
    (hbpos : 0 < ‖b‖) (hbunbounded : EssUnbounded b) :
    (∀ a : CriticalSobolev 1, Premise ν ε a → Reg ν a) ∧
    (∃ a : CriticalSobolev 1, Premise ν ε a) ∧
    (∃ a : CriticalSobolev 1,
      CriticalSigmaZero a ∧ 0 < ‖a‖ ∧ ‖a‖ < ε ∧
      calibratedScore ν a < 2 ∧ densityEssSup a = ⊤ ∧ Reg ν a) := by
  have hnonempty := ADMISSION_NONEMPTY_OF_ACTUAL_SEED ν ε hν hε b hb hbpos hbunbounded
  refine ⟨fun a ha => PREMISE_IMPLIES_REGULARITY ν ε hν a ha, hnonempty, ?_⟩
  obtain ⟨a, ha⟩ := hnonempty
  exact ⟨a, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1,
    (essUnbounded_iff_densityEssSup_eq_top a).mp ha.2.2.2.2,
    PREMISE_IMPLIES_REGULARITY ν ε hν a ha⟩

end
end SingularityDisprovement
