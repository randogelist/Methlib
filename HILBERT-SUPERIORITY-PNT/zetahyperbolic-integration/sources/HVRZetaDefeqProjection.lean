import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
Experimental direct expansion of the data fields of the zero-parameter
Hurwitz FE pair. In contrast to the previous simplified projection this
retains the original zero-parameter `if` expressions and composition syntax,
to test whether Lean's definitional equality can reduce the FE-pair proof
fields without referencing the pair itself in the new definition.

Neither the definition, the separate equality test, the axiom audit, nor the
dependency graph has yet been checked by an external Lean compiler. A zeta
value expression alone does not prove analyticity or the PNT.
-/
noncomputable section
open Complex Real Set MeasureTheory

namespace HVRZetaDefeqProjection

def zeroConstant : ℂ := if (0 : UnitAddCircle) = 0 then 1 else 0

def rawModifiedTheta : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => (Complex.ofReal ∘ HurwitzZeta.evenKernel 0) x - zeroConstant) +
    (Set.Ioo (0 : ℝ) 1).indicator
      (fun x : ℝ => (Complex.ofReal ∘ HurwitzZeta.evenKernel 0) x -
        ((1 : ℂ) * (↑(x ^ (-(1 / 2 : ℝ))) : ℂ)) • (1 : ℂ))

def rawLambda (s : ℂ) : ℂ :=
  mellin rawModifiedTheta s - (1 / s) • zeroConstant -
    ((1 : ℂ) / ((↑(1 / 2 : ℝ) : ℂ) - s)) • (1 : ℂ)

def rawZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (rawLambda (s / 2) / 2) / Gammaℝ s)
    0 (if (0 : UnitAddCircle) = 0 then -(1 : ℂ) / 2 else 0)

theorem rawZeta_apply (s : ℂ) :
    rawZeta s = Function.update (fun s : ℂ => (rawLambda (s / 2) / 2) / Gammaℝ s)
      0 (if (0 : UnitAddCircle) = 0 then -(1 : ℂ) / 2 else 0) s := rfl

end HVRZetaDefeqProjection
