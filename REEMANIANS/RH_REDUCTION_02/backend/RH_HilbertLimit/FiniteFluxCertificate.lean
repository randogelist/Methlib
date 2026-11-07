import RH_HilbertLimit.FiniteFluxInduction

/-!
# Finite raw certificate kernel for the Hilbert finite-flux route

This module introduces only finite raw data.  It does not assume RH, an
admissible cancellation budget, a local flux, or the uniform semantic step.
The interpreted flux is forced to vanish at row nine by construction.

`FiniteFluxWitness.syntaxCheck` is only a terminating structural checker for
this raw certificate format.  It is intentionally not yet the mathematical
soundness checker: the remaining frontier is to prove that an accepted finite
step certificate implies `FluxStepFromNine` for the actual Hilbert data.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- A finite arithmetic expression used to encode a candidate flux generator. -/
inductive FluxExpr where
  | const (q : ℚ)
  | row
  | col
  | add (a b : FluxExpr)
  | sub (a b : FluxExpr)
  | mul (a b : FluxExpr)
  deriving DecidableEq, Repr

namespace FluxExpr

/-- Exact finite node count of the expression tree. -/
def nodeCount : FluxExpr → ℕ
  | .const _ => 1
  | .row => 1
  | .col => 1
  | .add a b => 1 + nodeCount a + nodeCount b
  | .sub a b => 1 + nodeCount a + nodeCount b
  | .mul a b => 1 + nodeCount a + nodeCount b

/-- Semantic real evaluation of the finite expression. -/
def eval : FluxExpr → ℕ → ℕ → ℝ
  | .const q, _, _ => (q : ℝ)
  | .row, n, _ => (n : ℝ)
  | .col, _, j => (j : ℝ)
  | .add a b, n, j => eval a n j + eval b n j
  | .sub a b, n, j => eval a n j - eval b n j
  | .mul a b, n, j => eval a n j * eval b n j

/-- Decidable finite size guard used by the structural checker. -/
def withinNodeBudget (e : FluxExpr) (cap : ℕ) : Bool :=
  decide (e.nodeCount ≤ cap)

end FluxExpr

/-- The four finite branches that a future step-soundness certificate must cover. -/
inductive FluxRegion where
  | left
  | interior
  | right
  | boundary
  deriving DecidableEq, Repr

/-- One finite raw algebraic rule.  The multiplier is required to be
nonnegative by the structural checker; its mathematical interpretation is
left to the later soundness module. -/
structure FluxRule where
  region : FluxRegion
  slack : FluxExpr
  multiplier : ℚ
  deriving DecidableEq, Repr

/-- Finite raw data intended to certify the uniform step. -/
structure FluxStepCertificate where
  maxNodes : ℕ
  rules : List FluxRule
  deriving DecidableEq, Repr

namespace FluxRule

/-- Terminating structural validation of one finite rule. -/
def syntaxCheck (cap : ℕ) (r : FluxRule) : Bool :=
  r.slack.withinNodeBudget cap && decide (0 ≤ r.multiplier)

end FluxRule

namespace FluxStepCertificate

private def hasRegion (C : FluxStepCertificate) (region : FluxRegion) : Bool :=
  C.rules.any (fun r => decide (r.region = region))

/-- Terminating finite structural checker.  It checks a positive expression
budget, every rule's finite syntax/nonnegative rational multiplier, and the
presence of all four required step branches. -/
def syntaxCheck (C : FluxStepCertificate) : Bool :=
  decide (0 < C.maxNodes) &&
  C.rules.all (fun r => r.syntaxCheck C.maxNodes) &&
  C.hasRegion FluxRegion.left &&
  C.hasRegion FluxRegion.interior &&
  C.hasRegion FluxRegion.right &&
  C.hasRegion FluxRegion.boundary

end FluxStepCertificate

/-- The finite raw witness type for the new route.  Every field is finite raw
data; there are no `Prop`, function, or proof fields. -/
structure FiniteFluxWitness where
  coefficient : ℕ
  generator : FluxExpr
  stepCert : FluxStepCertificate
  deriving DecidableEq, Repr

namespace FiniteFluxWitness

/-- Structural finite check only.  This is deliberately not yet claimed to be
sound for the actual analytic flux step. -/
def syntaxCheck (W : FiniteFluxWitness) : Bool :=
  W.generator.withinNodeBudget W.stepCert.maxNodes && W.stepCert.syntaxCheck

/-- Semantic flux interpreted from finite raw generator data.  The `(n-9)`
factor makes the verified index-nine anchor definitional. -/
def flux (W : FiniteFluxWitness) (n j : ℕ) : ℝ :=
  ((n : ℝ) - 9) * W.generator.eval n j

/-- Every finite raw witness has the required zero anchor at row nine. -/
theorem flux_nine (W : FiniteFluxWitness) (j : ℕ) : W.flux 9 j = 0 := by
  simp [flux]

/-- The exact semantic statement that the future finite checker must establish. -/
def StepSound (W : FiniteFluxWitness) : Prop :=
  FluxStepFromNine W.coefficient W.flux

/-- Once the finite certificate is proved sound for the uniform step, the
already-audited Hilbert reduction yields literal Mathlib RH. -/
theorem nativeRH_of_stepSound (W : FiniteFluxWitness) (hstep : W.StepSound) :
    _root_.RiemannHypothesis := by
  exact nativeRH_of_finiteFlux_anchor_and_step W.coefficient W.flux
    W.flux_nine hstep

end FiniteFluxWitness

end RH_HilbertLimit
