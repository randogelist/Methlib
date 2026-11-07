import RH_HilbertLimit.FiniteFluxCertificate

/-!
# Finite algebraic checker kernel for the Hilbert finite-flux route

This module adds a genuinely finite Bool checker for finite algebraic
certificates.  It does **not** claim that the checker already proves the
actual Hilbert flux step.  The remaining mathematical frontier is the
interpretation bridge from the actual Bernstein/cancellation identities into
these finite regional certificates.

No `Prop`, proof, or function field is stored in the raw checked witness.
The checker validates only finite syntax, nonnegative rational multipliers,
and exact syntactic linear-combination identities.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- Finite symbolic expressions over finitely many numbered atoms.  The atoms
will be interpreted by the later actual Hilbert bridge. -/
inductive FluxProofExpr where
  | const (q : ℚ)
  | atom (i : ℕ)
  | add (a b : FluxProofExpr)
  | sub (a b : FluxProofExpr)
  | mul (a b : FluxProofExpr)
  deriving DecidableEq, Repr

namespace FluxProofExpr

/-- Exact finite node count. -/
def nodeCount : FluxProofExpr → ℕ
  | .const _ => 1
  | .atom _ => 1
  | .add a b => 1 + nodeCount a + nodeCount b
  | .sub a b => 1 + nodeCount a + nodeCount b
  | .mul a b => 1 + nodeCount a + nodeCount b

/-- Every atom index is strictly below the supplied finite arity. -/
def atomsBelow : FluxProofExpr → ℕ → Bool
  | .const _, _ => true
  | .atom i, arity => decide (i < arity)
  | .add a b, arity => atomsBelow a arity && atomsBelow b arity
  | .sub a b, arity => atomsBelow a arity && atomsBelow b arity
  | .mul a b, arity => atomsBelow a arity && atomsBelow b arity

/-- Structural finite guard for the proof-expression language. -/
def wellFormed (e : FluxProofExpr) (arity maxNodes : ℕ) : Bool :=
  e.atomsBelow arity && decide (e.nodeCount ≤ maxNodes)

/-- Semantic evaluation under an arbitrary real valuation of the finite atoms. -/
def eval : FluxProofExpr → (ℕ → ℝ) → ℝ
  | .const q, _ => (q : ℝ)
  | .atom i, ρ => ρ i
  | .add a b, ρ => eval a ρ + eval b ρ
  | .sub a b, ρ => eval a ρ - eval b ρ
  | .mul a b, ρ => eval a ρ * eval b ρ

end FluxProofExpr

/-- One finite nonnegative-multiplier premise used in an exact symbolic
linear-combination certificate. -/
structure WeightedFluxPremise where
  multiplier : ℚ
  premise : FluxProofExpr
  deriving DecidableEq, Repr

namespace WeightedFluxPremise

/-- The real value of one weighted premise under a valuation. -/
def evalTerm (t : WeightedFluxPremise) (ρ : ℕ → ℝ) : ℝ :=
  (t.multiplier : ℝ) * t.premise.eval ρ

end WeightedFluxPremise

namespace FluxProofExpr

/-- Exact syntax tree for the finite weighted sum.  No normalization oracle is
used: accepted certificates must provide this exact finite identity. -/
def sumScaled : List WeightedFluxPremise → FluxProofExpr
  | [] => .const 0
  | t :: ts => .add (.mul (.const t.multiplier) t.premise) (sumScaled ts)

/-- Generic soundness of the finite weighted-sum constructor. -/
theorem sumScaled_eval_nonneg
    (terms : List WeightedFluxPremise) (ρ : ℕ → ℝ)
    (hterms : ∀ t ∈ terms, 0 ≤ t.evalTerm ρ) :
    0 ≤ (sumScaled terms).eval ρ := by
  induction terms with
  | nil =>
      simp [sumScaled, eval]
  | cons t ts ih =>
      have ht : 0 ≤ t.evalTerm ρ := hterms t (by simp)
      have hts : ∀ s ∈ ts, 0 ≤ s.evalTerm ρ := by
        intro s hs
        exact hterms s (by simp [hs])
      have hrest : 0 ≤ (sumScaled ts).eval ρ := ih hts
      simpa [sumScaled, eval, WeightedFluxPremise.evalTerm] using
        add_nonneg ht hrest

end FluxProofExpr

/-- A finite exact algebraic certificate.  `goal` must be literally equal to
an exact weighted sum of the stored premises. -/
structure LinearFluxCertificate where
  arity : ℕ
  maxNodes : ℕ
  terms : List WeightedFluxPremise
  goal : FluxProofExpr
  deriving DecidableEq, Repr

namespace LinearFluxCertificate

/-- Purely finite validity predicate behind the terminating Bool checker. -/
def Valid (C : LinearFluxCertificate) : Prop :=
  0 < C.arity ∧
  0 < C.maxNodes ∧
  C.goal.wellFormed C.arity C.maxNodes = true ∧
  List.Forall
    (fun t =>
      t.premise.wellFormed C.arity C.maxNodes = true ∧
      0 ≤ t.multiplier)
    C.terms ∧
  C.goal = FluxProofExpr.sumScaled C.terms

instance (C : LinearFluxCertificate) : Decidable C.Valid := by
  unfold Valid
  infer_instance

/-- Terminating finite algebraic certificate checker. -/
def check (C : LinearFluxCertificate) : Bool :=
  decide C.Valid

@[simp] theorem check_eq_true_iff (C : LinearFluxCertificate) :
    C.check = true ↔ C.Valid := by
  simp [check]

/-- Generic semantic soundness: once each stored weighted premise is
nonnegative under a valuation, checker acceptance forces the checked goal to
be nonnegative under that valuation. -/
theorem sound
    (C : LinearFluxCertificate) (hcheck : C.check = true)
    (ρ : ℕ → ℝ)
    (hterms : ∀ t ∈ C.terms, 0 ≤ t.evalTerm ρ) :
    0 ≤ C.goal.eval ρ := by
  have hv : C.Valid := (check_eq_true_iff C).mp hcheck
  rcases hv with ⟨_, _, _, _, hgoal⟩
  rw [hgoal]
  exact FluxProofExpr.sumScaled_eval_nonneg C.terms ρ hterms

end LinearFluxCertificate

/-- Four finite algebraic certificates, one for each branch of the planned
uniform flux-step proof. -/
structure FluxRegionCertificates where
  left : LinearFluxCertificate
  interior : LinearFluxCertificate
  right : LinearFluxCertificate
  boundary : LinearFluxCertificate
  deriving DecidableEq, Repr

namespace FluxRegionCertificates

/-- Select the finite certificate corresponding to one region. -/
def get (C : FluxRegionCertificates) : FluxRegion → LinearFluxCertificate
  | .left => C.left
  | .interior => C.interior
  | .right => C.right
  | .boundary => C.boundary

/-- Finite validity of all four regional algebraic certificates. -/
def Valid (C : FluxRegionCertificates) : Prop :=
  C.left.check = true ∧
  C.interior.check = true ∧
  C.right.check = true ∧
  C.boundary.check = true

instance (C : FluxRegionCertificates) : Decidable C.Valid := by
  unfold Valid
  infer_instance

/-- Terminating checker for the four finite branches. -/
def check (C : FluxRegionCertificates) : Bool :=
  decide C.Valid

@[simp] theorem check_eq_true_iff (C : FluxRegionCertificates) :
    C.check = true ↔ C.Valid := by
  simp [check]

/-- Acceptance of all four branches implies acceptance of the selected one. -/
theorem get_check_of_check
    (C : FluxRegionCertificates) (region : FluxRegion)
    (h : C.check = true) :
    (C.get region).check = true := by
  have hv : C.Valid := (check_eq_true_iff C).mp h
  rcases hv with ⟨hl, hi, hr, hb⟩
  cases region with
  | left => exact hl
  | interior => exact hi
  | right => exact hr
  | boundary => exact hb

end FluxRegionCertificates

/-- The checked finite witness.  Every stored field remains finite raw data. -/
structure FiniteFluxCheckedWitness where
  raw : FiniteFluxWitness
  regions : FluxRegionCertificates
  deriving DecidableEq, Repr

namespace FiniteFluxCheckedWitness

/-- Exact finite validity predicate: structural raw-witness acceptance plus all
four algebraic regional certificates. -/
def Valid (W : FiniteFluxCheckedWitness) : Prop :=
  W.raw.syntaxCheck = true ∧ W.regions.check = true

instance (W : FiniteFluxCheckedWitness) : Decidable W.Valid := by
  unfold Valid
  infer_instance

/-- The terminating finite checker for the algebraic certificate layer. -/
def check (W : FiniteFluxCheckedWitness) : Bool :=
  decide W.Valid

@[simp] theorem check_eq_true_iff (W : FiniteFluxCheckedWitness) :
    W.check = true ↔ W.Valid := by
  simp [check]

/-- Generic regional checker soundness.  The later actual Hilbert bridge only
has to instantiate the finite atoms and prove the stored weighted premises are
nonnegative. -/
theorem region_sound
    (W : FiniteFluxCheckedWitness) (hcheck : W.check = true)
    (region : FluxRegion) (ρ : ℕ → ℝ)
    (hterms : ∀ t ∈ (W.regions.get region).terms,
      0 ≤ t.evalTerm ρ) :
    0 ≤ (W.regions.get region).goal.eval ρ := by
  have hv : W.Valid := (check_eq_true_iff W).mp hcheck
  have hregion : (W.regions.get region).check = true :=
    W.regions.get_check_of_check region hv.2
  exact (W.regions.get region).sound hregion ρ hterms

/-- The remaining actual mathematical bridge for the checked witness. -/
def StepSound (W : FiniteFluxCheckedWitness) : Prop :=
  W.raw.StepSound

/-- Exact noncircular soundness target for the next module. -/
def CheckerSoundnessTarget (W : FiniteFluxCheckedWitness) : Prop :=
  W.check = true → W.StepSound

/-- Once the actual interpretation bridge proves `StepSound`, the previously
audited semantic Hilbert endpoint yields literal Mathlib RH. -/
theorem nativeRH_of_stepSound
    (W : FiniteFluxCheckedWitness) (hstep : W.StepSound) :
    _root_.RiemannHypothesis := by
  exact W.raw.nativeRH_of_stepSound hstep

end FiniteFluxCheckedWitness

end RH_HilbertLimit
