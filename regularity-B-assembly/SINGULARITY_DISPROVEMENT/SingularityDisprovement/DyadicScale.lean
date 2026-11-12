import SingularityDisprovement.Scaling
import SingularityDisprovement.Dyadic

/-! The scale-existence endpoint instantiated at the literal constructed datum.
All carrier, solenoidality and nonzero-norm premises are discharged. -/

set_option autoImplicit false
set_option Elab.async true

namespace SingularityDisprovement
open SingularClosure
noncomputable section

theorem DYADIC_ADMITTED_SCALE (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧
      0 < ‖((1 / 2 : ℝ) ^ m) • dyadicSeed ν‖ ∧
      ‖((1 / 2 : ℝ) ^ m) • dyadicSeed ν‖ < ε ∧
      calibratedScore ν (((1 / 2 : ℝ) ^ m) • dyadicSeed ν) < 1 :=
  SMALL_POSITIVE_DYADIC_SCALE_EXISTS ν ε hν hε (dyadicSeed ν)
    (dyadicSeed_sigma ν) (dyadicSeed_norm_pos hν)

end
end SingularityDisprovement
