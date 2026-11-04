import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
Scoped divisor-sum reconstruction via prime-power divisor enumeration.
This follows Mathlib's divisor-enumeration argument in
Mathlib/NumberTheory/Divisors.lean, Copyright (c) 2020 Aaron Anderson,
Apache License 2.0. No independence from generic finite-set/divisor lemmas
is asserted. This exact source requires an external Lean audit.
-/

namespace HVRNativePrimePowerDivisorSum

open scoped BigOperators

theorem sum_divisors_prime_pow {α : Type*} [AddCommMonoid α]
    {p k : ℕ} {f : ℕ → α} (hp : p.Prime) :
    (∑ d ∈ (p ^ k).divisors, f d) = ∑ j ∈ Finset.range (k + 1), f (p ^ j) := by
  simp only [Nat.divisors_prime_pow hp k, Finset.sum_map]
  rfl

end HVRNativePrimePowerDivisorSum
