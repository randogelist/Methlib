import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
The divisor expression for multiplication by the arithmetic zeta function,
specialized to the von Mangoldt function. The proof uses the defining
divisor-antidiagonal convolution and a finite set reindexing; it does not
explicitly invoke `ArithmeticFunction.coe_mul_zeta_apply`.

Adapted from Mathlib's arithmetic zeta and divisors development at revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0. This source is a candidate until
compiled and audited on an external cached Lean installation. It retains
Mathlib definitions, finite-set reindexing and divisor infrastructure.
-/

noncomputable section
open Finset Nat

namespace HVRNativeArithmeticZeta

theorem mangoldt_mul_zeta_apply (n : ℕ) :
    (ArithmeticFunction.vonMangoldt * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
      ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
  rw [ArithmeticFunction.mul_apply]
  trans ∑ i ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt i.fst
  · refine sum_congr rfl fun i hi => ?_
    rcases mem_divisorsAntidiagonal.1 hi with ⟨rfl, h⟩
    rw [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (right_ne_zero_of_mul h), cast_one, mul_one]
  · rw [← map_div_right_divisors, sum_map] <;> rfl

end HVRNativeArithmeticZeta
