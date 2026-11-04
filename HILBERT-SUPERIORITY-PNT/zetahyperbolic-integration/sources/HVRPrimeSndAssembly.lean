import HVRPrimeKernelTrace
import HVRTwoPrimeGram
import HVRPrimeMomentDecay
import HVR_Snditeration_PrimePowerTail

/-!
Prime-specific finite-dimensional assembly of the snditeration moment and
Laplace-kernel ideas. The cutoff contains primes 2 and 3, so the dimension-two
determinant premise is discharged. This is a candidate until the exact source
passes a cached external Lean build and theorem-level audit. It is not connected
to the PNT root and makes no zeta or infinite-cutoff assertion.
-/

noncomputable section
open scoped BigOperators

namespace HVRPrimeSndAssembly

theorem two_prime_logDet_kernel_hasDerivAt (N : ℕ) (σ : ℝ) (hN : 3 ≤ N) :
    HasDerivAt
      (fun z : ℝ => Real.log ((HVRPrimeMomentJacobi.gram N 2 z).det))
      (-(∑ p ∈ HVRPrimeGram.primesUpTo N,
        HVRPrimeGram.primeWeight σ p * Real.log (p : ℝ) *
          HVRPrimeKernelTrace.diagonalKernel N 2 σ p)) σ :=
  HVRPrimeKernelTrace.prime_gram_logDet_kernel_hasDerivAt N 2 σ
    (ne_of_gt (HVRTwoPrimeGram.gram_det_pos N σ hN))

end HVRPrimeSndAssembly
