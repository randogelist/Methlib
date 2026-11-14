import OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound
import AttemptE

/-!
Exact external endpoint: upstream OpenAI/math Lean 4.34.1 commit
4eaee87548250b2682affda7d05d947c05554bae.
-/

namespace Erdos687AttemptE

theorem imported_jacobsthal_quadratic : JacobsthalQuadratic := by
  exact OAI.Erdos970.Erdos970Final.erdos_970_quadratic

theorem imported_prime_cutoff_quadratic :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℕ, 2 ≤ x →
        ∃ m : ℕ, (m : ℝ) ≤ C * (primeCount x : ℝ) ^ 2 ∧
          ∀ H : ℕ, m ≤ H →
            ¬ CoveredBlock (primorial x) H ∧
            coveredCount (primorial x) H = 0 ∧
            momentCertificate (primorial x) H = 0 ∧
            finiteCheck (primorial x) H = true := by
  exact quadratic_prime_cutoff imported_jacobsthal_quadratic

#print axioms Erdos687AttemptE.imported_jacobsthal_quadratic
#print axioms Erdos687AttemptE.imported_prime_cutoff_quadratic

end Erdos687AttemptE
