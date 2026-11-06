import AIM939.Diagonal
import AIM939.FiniteWitness

/-!
Full counterexample to the n=p=4 specialization of AIM939.
The coefficient vector is strictly positive.  The diagonal fourth root is
concave on the complete positive half-line, while the full fourth root
fails the midpoint inequality at explicitly certified interior points.

No conjectural certificate or analytic admission is a theorem premise.
Prepared candidate: external native build and axiom audit remain pending.
-/

noncomputable section

namespace AIM939

theorem exists_counterexample :
    ∃ a : Fin 5 → ℝ,
      (∀ k, 0 < a k) ∧
      ConcaveOn ℝ (Set.Ioi (0 : ℝ))
        (fun t => rootQuarter (fOf a (fun _ => t))) ∧
      ¬ ConcaveOn ℝ orthant (fun x => rootQuarter (fOf a x)) := by
  refine ⟨coefficients, coefficients_pos, ?_, ?_⟩
  · simpa only [fOf_coefficients, f_diagonal] using diagonal_concave
  · simpa only [fOf_coefficients] using not_concaveOn_rootQuarter_f

/-- The original implication already fails when n=p=4. -/
theorem AIM939_COUNTEREXAMPLE : ¬ DiagonalConcavityAssertion4 := by
  intro hclaim
  rcases exists_counterexample with ⟨a, hpos, hdiag, hfail⟩
  exact hfail (hclaim a (fun k => (hpos k).le)
    ⟨0, ne_of_gt (hpos 0)⟩ hdiag)

end AIM939
