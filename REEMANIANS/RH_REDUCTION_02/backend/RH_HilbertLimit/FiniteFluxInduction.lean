import RH_HilbertLimit.ZeroBudgetTenRows
import RH_HilbertLimit.ActualCancellationWitness

/-!
# Finite-flux induction reduction from the verified index-nine seed

The first ten cancellation indices are already established by the imported
zero-budget row analysis.  This module changes the forward strategy: exact
zero propagation is no longer required.  Instead a finite natural coefficient
`K` is paired with a rowwise telescoping flux.  A uniform one-step propagation
law for that rowwise flux, anchored at index nine, gives an admissible
cancellation budget and hence literal Mathlib `RiemannHypothesis` through the
existing Hilbert-limit endpoint.

The flux function and propagation law in this module are semantic data.  They
are deliberately not a finite raw witness and not a terminating Bool checker.
This module is the reduction theorem to which a later finite certificate
checker must be sound.

No local Lean, Lake, or CI execution was performed while preparing this source.
Native Windows Lean 4.33.0 compilation and axiom audit remain required.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- The cancellation budget used by the finite-flux route starts exactly at
index nine; only the natural coefficient is variable. -/
def finiteFluxBudget (K : ℕ) : CancellationBudget := ⟨9, K⟩

/-- A single row satisfies the local telescoping flux inequalities.  This is a
semantic predicate; `H` is still an unrestricted mathematical function. -/
def CancellationBudget.FluxGood
    (W : CancellationBudget) (H : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ j : ℕ, j ≤ n →
    cancellationDefect actualNormalizedMoment n j ≤
      (W.coefficient : ℝ) * |actualWeight n j| +
        (H n (j + 1) - H n j)) ∧
  H n (n + 1) ≤ H n 0

/-- A zero row cancellation forces every in-range cancellation defect to
vanish, since the row is a finite sum of nonnegative defects. -/
theorem cancellationDefect_eq_zero_of_rowCancellation_eq_zero
    (u : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n)
    (hrow : rowCancellation u n = 0) :
    cancellationDefect u n j = 0 := by
  have hsum :
      (∑ k ∈ Finset.range (n + 1), cancellationDefect u n k) = 0 := by
    simpa [rowCancellation] using hrow
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => cancellationDefect_nonneg u n k (by
        have hklt := Finset.mem_range.mp hk
        omega))).mp hsum
  exact hterms j (Finset.mem_range.mpr (by omega))

/-- One good local-flux row yields the scalar cancellation-budget inequality
for that row by the generic telescoping identity. -/
theorem CancellationBudget.rowCancellation_le_of_fluxGood
    (W : CancellationBudget) (H : ℕ → ℕ → ℝ) (n : ℕ)
    (hgood : W.FluxGood H n) :
    rowCancellation actualNormalizedMoment n ≤
      (W.coefficient : ℝ) * actualVariation n := by
  exact rowCancellation_le_of_local_flux actualNormalizedMoment n
    (W.coefficient : ℝ) (H n) hgood.1 hgood.2

/-- If the semantic flux is anchored to zero on row nine, the already verified
zero cancellation at index nine supplies the base local-flux row for every
natural coefficient `K`. -/
theorem finiteFluxBudget_fluxGood_nine_of_anchor
    (K : ℕ) (H : ℕ → ℕ → ℝ)
    (hanchor : ∀ j : ℕ, H 9 j = 0) :
    (finiteFluxBudget K).FluxGood H 9 := by
  constructor
  · intro j hj
    have hrow : rowCancellation actualNormalizedMoment 9 = 0 :=
      zeroBudgetCandidate_first_ten_cancellations 9 (by omega)
    have hdef : cancellationDefect actualNormalizedMoment 9 j = 0 :=
      cancellationDefect_eq_zero_of_rowCancellation_eq_zero
        actualNormalizedMoment 9 j hj hrow
    rw [hdef, hanchor (j + 1), hanchor j]
    simp only [sub_self, add_zero]
    exact mul_nonneg (Nat.cast_nonneg K) (abs_nonneg _)
  · rw [hanchor (9 + 1), hanchor 0]

/-- The only infinite semantic obligation left by this reduction: from index
nine onward, a good local-flux row propagates to the next row. -/
def FluxStepFromNine (K : ℕ) (H : ℕ → ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 9 ≤ n →
    (finiteFluxBudget K).FluxGood H n →
    (finiteFluxBudget K).FluxGood H (n + 1)

/-- The index-nine anchor plus the uniform flux step gives the full semantic
local-flux predicate for the finite budget `⟨9,K⟩`. -/
theorem finiteFluxBudget_localFlux_of_anchor_and_step
    (K : ℕ) (H : ℕ → ℕ → ℝ)
    (hanchor : ∀ j : ℕ, H 9 j = 0)
    (hstep : FluxStepFromNine K H) :
    (finiteFluxBudget K).LocalFlux H := by
  have hall : ∀ n : ℕ, 9 ≤ n → (finiteFluxBudget K).FluxGood H n := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn
        by_cases hprev : 9 ≤ n
        · exact hstep n hprev (ih hprev)
        · have hsum : n + 1 = 9 := by omega
          exact hsum.symm ▸ finiteFluxBudget_fluxGood_nine_of_anchor K H hanchor
  constructor
  · intro n hn
    change 9 ≤ n at hn
    exact (hall n hn).1
  · intro n hn
    change 9 ≤ n at hn
    exact (hall n hn).2

/-- The semantic anchored flux-step hypothesis already suffices for an
admissible finite natural cancellation budget. -/
theorem finiteFluxBudget_admissible_of_anchor_and_step
    (K : ℕ) (H : ℕ → ℕ → ℝ)
    (hanchor : ∀ j : ℕ, H 9 j = 0)
    (hstep : FluxStepFromNine K H) :
    (finiteFluxBudget K).Admissible := by
  exact cancellationBudget_admissible_of_local_flux (finiteFluxBudget K) H
    (finiteFluxBudget_localFlux_of_anchor_and_step K H hanchor hstep)

/-- B-tier forward endpoint for the new route.  Once a finite terminating
checker is proved sound for the anchored uniform flux step, the remaining
Hilbert-limit chain to literal Mathlib RH is already complete. -/
theorem nativeRH_of_finiteFlux_anchor_and_step
    (K : ℕ) (H : ℕ → ℕ → ℝ)
    (hanchor : ∀ j : ℕ, H 9 j = 0)
    (hstep : FluxStepFromNine K H) :
    _root_.RiemannHypothesis := by
  exact nativeRH_of_admissible_cancellationBudget (finiteFluxBudget K)
    (finiteFluxBudget_admissible_of_anchor_and_step K H hanchor hstep)

/-- Existential semantic form of the same reduction.  This is intentionally
not yet the finite-witness theorem because `H` and `FluxStepFromNine` are
infinite semantic objects. -/
theorem nativeRH_of_exists_finiteFlux_semantic_step
    (h : ∃ K : ℕ, ∃ H : ℕ → ℕ → ℝ,
      (∀ j : ℕ, H 9 j = 0) ∧ FluxStepFromNine K H) :
    _root_.RiemannHypothesis := by
  obtain ⟨K, H, hanchor, hstep⟩ := h
  exact nativeRH_of_finiteFlux_anchor_and_step K H hanchor hstep

end RH_HilbertLimit
