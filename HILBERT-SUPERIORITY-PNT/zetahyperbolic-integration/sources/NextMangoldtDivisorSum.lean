import HVRNativePrimePowerDivisorSum
import HVRNativeCoprimePrimePowerDivisors
import HVRNativeArithmeticZeta
import HVRSimpleMangoldtOne
import HVRSimplePrimePowDisjoint
import NativeMangoldtPrime
import NativeMangoldtPow
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
Source candidate only: rebuild the classical divisor-sum and convolution
identities using the earlier native prime/power value lemmas. These arguments
use generic prime factorization and divisor-sum infrastructure. No local Lean
run has been performed. Verify exact compilation, axioms, and dependencies.
-/

noncomputable section
open Finset Nat
open scoped ArithmeticFunction ArithmeticFunction.zeta

namespace HVRNextMangoldtDivisorSum

theorem vonMangoldt_sum_native {n : ℕ} :
    ∑ i ∈ n.divisors, ArithmeticFunction.vonMangoldt i = Real.log n := by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [HVRNativePrimePowerDivisorSum.sum_divisors_prime_pow hp, Nat.cast_pow, Real.log_pow, Finset.sum_range_succ',
      Nat.pow_zero, HVRSimpleMangoldtOne.vonMangoldt_one]
    simp [HVRNativeMangoldtPow.vonMangoldt_apply_pow_native (Nat.succ_ne_zero _),
      HVRNativeMangoldtPrime.vonMangoldt_apply_prime_native hp]
  intro a b ha' hb' hab ha hb
  simp only [ArithmeticFunction.vonMangoldt_apply, ← Finset.sum_filter] at ha hb ⊢
  rw [HVRNativeCoprimePrimePowerDivisors.filtered_divisors_mul hab, filter_union,
    sum_union (HVRSimplePrimePowDisjoint.disjoint_divisors hab), ha, hb, Nat.cast_mul,
    Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]

theorem vonMangoldt_mul_zeta_native :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) *
      ArithmeticFunction.zeta = ArithmeticFunction.log := by
  ext n
  rw [HVRNativeArithmeticZeta.mangoldt_mul_zeta_apply, vonMangoldt_sum_native]
  rfl

end HVRNextMangoldtDivisorSum
