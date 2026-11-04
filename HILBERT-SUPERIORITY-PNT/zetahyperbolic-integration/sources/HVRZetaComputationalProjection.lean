import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
Candidate computational-field expansion of the pinned actual zeta value.
The modified theta function and Mellin expression below spell out only the
data fields of the zero-parameter weak FE pair. No functional-equation proof
field occurs explicitly in these definitions.

Neither the expanded definition, its relation to Mathlib's actual zeta, nor
its dependency trace has been checked by an external Lean run. In particular,
`HurwitzZeta.evenKernel` and `Complex.Gammaℝ` may themselves carry the
target dependency. The equality theorem's type explicitly mentions
`riemannZeta`, and therefore is expected to reach that constant and its own
dependencies under the declaration-graph metric.
-/
noncomputable section
open Complex Real Set MeasureTheory

namespace HVRZetaComputationalProjection

def modifiedTheta : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator
      (fun x : ℝ => (HurwitzZeta.evenKernel 0 x : ℂ) - 1) +
    (Set.Ioo (0 : ℝ) 1).indicator
      (fun x : ℝ => (HurwitzZeta.evenKernel 0 x : ℂ) -
        ((1 : ℂ) * (↑(x ^ (-(1 / 2 : ℝ))) : ℂ)) • (1 : ℂ))

def projectedLambda (s : ℂ) : ℂ :=
  mellin modifiedTheta s - (1 / s) • (1 : ℂ) -
    ((1 : ℂ) / ((↑(1 / 2 : ℝ) : ℂ) - s)) • (1 : ℂ)

/-- Fully explicit value expression, including Mathlib's totalized value at 0. -/
def projectedZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (projectedLambda (s / 2) / 2) / Gammaℝ s)
    0 (-(1 : ℂ) / 2)

theorem projectedZeta_apply (s : ℂ) : projectedZeta s =
    Function.update (fun z : ℂ => (projectedLambda (z / 2) / 2) / Gammaℝ z)
      0 (-(1 : ℂ) / 2) s := rfl

end HVRZetaComputationalProjection
