import SingularityDisprovement.RootAssembly
import SingularityDisprovement.DyadicUnbounded

/-! The exact selected root: calibrated admission implies regularity and the
antecedent is inhabited by an actual essentially unbounded critical datum.
All concrete dyadic prerequisites are imported, never assumed here. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal

namespace SingularityDisprovement
open SingularClosure
noncomputable section

theorem ADMISSION_NONEMPTY (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    ∃ a : CriticalSobolev 1, Premise ν ε a :=
  ADMISSION_NONEMPTY_OF_ACTUAL_SEED ν ε hν hε (dyadicSeed ν)
    (dyadicSeed_sigma ν) (dyadicSeed_norm_pos hν) (dyadicSeed_essUnbounded ν hν)

theorem SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN
    (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    (∀ a : CriticalSobolev 1, Premise ν ε a → Reg ν a) ∧
    (∃ a : CriticalSobolev 1, Premise ν ε a) ∧
    (∃ a : CriticalSobolev 1,
      CriticalSigmaZero a ∧ 0 < ‖a‖ ∧ ‖a‖ < ε ∧
      calibratedScore ν a < 2 ∧ densityEssSup a = ⊤ ∧ Reg ν a) :=
  REGULARITY_CHAIN_OF_ACTUAL_SEED ν ε hν hε (dyadicSeed ν)
    (dyadicSeed_sigma ν) (dyadicSeed_norm_pos hν) (dyadicSeed_essUnbounded ν hν)

end
end SingularityDisprovement
