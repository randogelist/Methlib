import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
Prime-power support regrouping for the complex-valued series used in the HVR
zeta bridge. The proof expands the reindexing step using the bijection between
prime powers and pairs `(p,k)`, and generic summability and equivalence tools.

This is a source candidate. It has not been compiled or theorem-audited. It
does not explicitly invoke `tsum_eq_tsum_primes_of_support_subset_prime_powers`
or `tsum_primes_pow_eq`; transitive dependencies still need a diagnostic audit.

Adapted from the prime-power reindexing proof in Mathlib
`Mathlib/NumberTheory/EulerProduct/Basic.lean` at revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0.
Copyright (c) 2023 Michael Stoll. Released under Apache License 2.0.
-/

noncomputable section
open scoped BigOperators
open Nat.Primes

namespace HVRNativePrimePowerRegroup

/-- A summable complex sequence supported on prime powers can be summed by
prime base and positive exponent. -/
theorem regroup {f : ℕ → ℂ} (hsum : Summable f)
    (hsupport : Function.support f ⊆ {n : ℕ | IsPrimePow n}) :
    (∑' n : ℕ, f n) = ∑' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1)) := by
  have hsub : Summable (fun n : {n : ℕ // IsPrimePow n} => f n.1) :=
    hsum.subtype _
  have hindex :
      (∑' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1))) =
        ∑' n : {n : ℕ // IsPrimePow n}, f n.1 := by
    calc
      _ = ∑' pk : Nat.Primes × ℕ, f (prodNatEquiv pk) := by
        simpa using (hsub.comp_injective prodNatEquiv.injective).tsum_prod.symm
      _ = _ := by rw [← Equiv.tsum_eq prodNatEquiv]
  exact (tsum_subtype_eq_of_support_subset hsupport).symm.trans hindex.symm

end HVRNativePrimePowerRegroup
