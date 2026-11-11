import SingularClosure.CriticalSpacesCutoff
import SingularClosure.CriticalLimit
import SingularClosure.GalerkinExistence

/-! Actual finite Galerkin trajectories in every half-order Sobolev space. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal

namespace SingularClosure

noncomputable section

def criticalFiniteStateComplexLinear (q : ℤ) (N : ℕ) :
    FiniteGalerkinState N →ₗ[ℂ] CriticalSobolev q where
  toFun z := criticalFiniteSobolev q N (extendFiniteState N z)
  map_add' z w := by
    apply criticalCoeff_injective q
    rw [criticalCoeff_add, criticalFiniteSobolev_coeff,
      criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff]
    funext k i
    by_cases hk : k ∈ cutoffModes N <;>
      simp [cutoffCoeff, extendFiniteState, hk]
  map_smul' r z := by
    apply criticalCoeff_injective q
    rw [criticalCoeff_smul, criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff]
    funext k i
    by_cases hk : k ∈ cutoffModes N <;>
      simp [cutoffCoeff, extendFiniteState, hk]

def criticalFiniteState (q : ℤ) (N : ℕ) :
    FiniteGalerkinState N →L[ℝ] CriticalSobolev q :=
  ((criticalFiniteStateComplexLinear q N).restrictScalars ℝ).toContinuousLinearMap

theorem criticalFiniteState_apply (q : ℤ) (N : ℕ) (z : FiniteGalerkinState N) :
    criticalFiniteState q N z = criticalFiniteSobolev q N (extendFiniteState N z) := rfl

theorem criticalFiniteState_restrict (q : ℤ) (N : ℕ) (c : FourierCoeff) :
    criticalFiniteState q N (restrictFiniteState N c) = criticalFiniteSobolev q N c := by
  rw [criticalFiniteState_apply]
  apply criticalCoeff_injective q
  rw [criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff,
    extend_restrictFiniteState, cutoffCoeff_idempotent]

def GalerkinSolution.criticalState {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (q : ℤ) (t : ℝ) : CriticalSobolev q :=
  criticalFiniteSobolev q N (g.coeff t)

theorem GalerkinSolution.criticalState_coeff {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (q : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    criticalCoeff q (g.criticalState q t) = g.coeff t := by
  change criticalCoeff q (criticalFiniteSobolev q N (g.coeff t)) = _
  rw [criticalFiniteSobolev_coeff, g.cutoffCoeff_eq t ht]

theorem GalerkinSolution.criticalState_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (q : ℤ) :
    ContinuousOn (g.criticalState q) (Ici 0) := by
  have h := (criticalFiniteState q N).continuous.comp_continuousOn g.finite_continuousOn
  simpa only [Function.comp_def, criticalFiniteState_restrict,
    GalerkinSolution.criticalState] using! h

def GalerkinSolution.criticalRhs {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (q : ℤ) (t : ℝ) : CriticalSobolev q :=
  criticalFiniteState q N (finiteGalerkinRhs ν N (restrictFiniteState N (g.coeff t)))

theorem GalerkinSolution.criticalRhs_eq_finiteSobolev
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    g.criticalRhs q t = criticalFiniteSobolev q N (galerkinRhs ν N (g.coeff t)) := by
  change criticalFiniteState q N
      (restrictFiniteState N (galerkinRhs ν N
        (extendFiniteState N (restrictFiniteState N (g.coeff t))))) = _
  rw [criticalFiniteState_restrict, g.extend_restrict_coeff t ht]

theorem GalerkinSolution.criticalRhs_coeff
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℤ) (t : ℝ) (ht : 0 ≤ t) {k : Frequency} (hk : k ∈ cutoffModes N)
    (i : Fin 3) :
    criticalCoeff q (g.criticalRhs q t) k i = galerkinRhs ν N (g.coeff t) k i := by
  rw [g.criticalRhs_eq_finiteSobolev q t ht, criticalFiniteSobolev_coeff]
  simp only [cutoffCoeff, if_pos hk]

theorem GalerkinSolution.criticalState_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (g.criticalState q) (g.criticalRhs q t) (Ici 0) t := by
  have h := (criticalFiniteState q N).hasFDerivAt.comp_hasDerivWithinAt t
    (g.finite_hasDerivWithinAt ht)
  simpa only [Function.comp_def, criticalFiniteState_restrict,
    GalerkinSolution.criticalState, GalerkinSolution.criticalRhs] using! h

theorem GalerkinSolution.criticalRhs_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (q : ℤ) :
    ContinuousOn (g.criticalRhs q) (Ici 0) := by
  have h := ((criticalFiniteState q N).continuous.comp
    (contDiff_finiteGalerkinRhs ν N).continuous).comp_continuousOn g.finite_continuousOn
  simpa only [Function.comp_def, GalerkinSolution.criticalRhs] using! h

/-- The actual finite states and actual negative-order derivatives suffice for
one common Fourier subsequence; no auxiliary realizations are premises. -/
theorem CRITICAL_GALERKIN_FOURIER_COMPACTNESS
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstate : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(g n).criticalState 1 t‖ ≤ A)
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ B) :
    ∃ u : FourierIndex → C(Icc (0 : ℝ) T, ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k i,
        TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
          (g (φ n)).coeff t.val k i) (u (k, i)) atTop := by
  apply CRITICAL_GALERKIN_COEFFICIENT_SUBSEQUENCE ν a N g
    (fun n => (g n).criticalState 1) (fun n => (g n).criticalRhs (-1)) T A B hA hB
  · intro n t ht
    exact (g n).criticalState_coeff 1 ht
  · intro n
    exact ((g n).criticalRhs_continuousOn (-1)).mono (fun t ht => ht.1)
  · intro n t ht k hk i
    exact (g n).criticalRhs_coeff (-1) t ht.1 hk i
  · exact hstate
  · exact hbudget

end

end SingularClosure
