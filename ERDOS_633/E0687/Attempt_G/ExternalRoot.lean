import OAI.NumberTheory.Jacobsthal.Main
import AttemptG.FiniteBridge

/-!
External-root adapter pinned by the CI workflow to openai/math
commit 4eaee87548250b2682affda7d05d947c05554bae.
No new axioms, sorry, or opaque proof substitutions.
-/

namespace Erdos687AttemptG

/-- Definitional transfer from the verified external Jacobsthal theorem. -/
theorem external_jacobsthal_quadratic :
    JacobsthalQuadratic := by
  obtain ⟨C, hC, hbound⟩ :=
    OAI.Erdos970.Erdos970Final.erdos_970_quadratic
  refine ⟨C, hC, ?_⟩
  intro k hk
  obtain ⟨m, hm, hmbound⟩ := hbound k hk
  refine ⟨m, ?_, hmbound⟩
  intro n hn hcard a
  exact hm n hn hcard a

/-- #687 Attempt_G root:
  for all positive n with at most k prime factors, the length-m
  covering obstruction is excluded, all survivor counts are positive,
  and every finite translated Gram form is nonnegative, with m <= C k^2. -/
theorem erdos_687_prime_hankel_external_root :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ, (m : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
        ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
          (¬ coverableByPrimeFactors n m) ∧
          (∀ a : ℤ, 0 < survivorCount n m a) ∧
          (∀ A : Finset ℤ, ∀ f : ℕ → ℤ,
            0 ≤ gramForm A n m f) := by
  exact jacobsthal_quadratic_to_prime_gram
    external_jacobsthal_quadratic

end Erdos687AttemptG

#print axioms Erdos687AttemptG.external_jacobsthal_quadratic
#print axioms Erdos687AttemptG.erdos_687_prime_hankel_external_root
