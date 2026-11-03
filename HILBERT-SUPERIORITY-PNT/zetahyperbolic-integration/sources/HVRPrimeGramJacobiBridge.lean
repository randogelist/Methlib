import HVRPrimeAtomicGram
import HVR_PrimeMomentJacobi

/-!
Identifies the finite prime-node Gram quadratic construction with the finite
prime-moment matrix used in the Zetahyperbolic Jacobi adaptation.
The positivity established here is nonnegative; strict positivity needs the
explicit nonvanishing prime-node witness.  No infinite-limit or PNT claim.
-/

noncomputable section
open scoped BigOperators

namespace HVRPrimeGramJacobiBridge

/-- Both packages use exactly the same finite prime-moment matrix entries. -/
theorem gramEntry_eq_primeMomentGram (N h : ℕ) (sigma : ℝ) (i j : Fin h) :
    HVRPrimeAtomicGram.gramEntry N sigma h i j =
      HVRPrimeMomentJacobi.gram N h sigma i j := by
  change
    (∑ p ∈ HVRPrimeGram.primesUpTo N,
      HVRPrimeGram.primeWeight sigma p *
        (Real.log (p : ℝ)) ^ i.val * (Real.log (p : ℝ)) ^ j.val) =
      ∑ p ∈ HVRPrimeGram.primesUpTo N,
        HVRPrimeGram.primeWeight sigma p *
          (Real.log (p : ℝ)) ^ (i.val + j.val)
  apply Finset.sum_congr rfl
  intro p hp
  rw [pow_add]
  ring

/-- The Jacobi package's actual prime-moment matrix has a nonnegative
quadratic form for every cutoff, dimension and real coefficient vector. -/
theorem primeMomentGram_quadratic_nonnegative (N h : ℕ) (sigma : ℝ)
    (c : Fin h → ℝ) :
    0 ≤ ∑ i : Fin h, ∑ j : Fin h,
      c i * HVRPrimeMomentJacobi.gram N h sigma i j * c j := by
  have hpos := HVRPrimeAtomicGram.quadratic_nonnegative N sigma h c
  unfold HVRPrimeAtomicGram.quadratic at hpos
  simpa only [gramEntry_eq_primeMomentGram] using hpos

/-- A visible nonzero node gives strict positivity of the Jacobi package's
quadratic form.  Existence of such a node is an explicit hypothesis. -/
theorem primeMomentGram_quadratic_pos_of_prime_witness
    (N h : ℕ) (sigma : ℝ) (c : Fin h → ℝ) {p : ℕ}
    (hp : p ∈ HVRPrimeGram.primesUpTo N)
    (hnode : HVRPrimeAtomicGram.evalFeature c p ≠ 0) :
    0 < ∑ i : Fin h, ∑ j : Fin h,
      c i * HVRPrimeMomentJacobi.gram N h sigma i j * c j := by
  have hpos :=
    HVRPrimeAtomicGram.quadratic_pos_of_prime_witness N sigma h c hp hnode
  unfold HVRPrimeAtomicGram.quadratic at hpos
  simpa only [gramEntry_eq_primeMomentGram] using hpos

end HVRPrimeGramJacobiBridge
