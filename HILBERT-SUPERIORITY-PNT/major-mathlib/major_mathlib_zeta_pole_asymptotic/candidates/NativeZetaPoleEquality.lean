import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-!
Candidate logarithmic-derivative identity from the regularized zeta factor.
The proof reconstructs the local algebra from separate Mathlib factorization,
derivative, and nonvanishing statements. It does not call the corresponding
pre-existing eventual logarithmic-derivative identity. The factorization and
derivative results remain Mathlib dependencies. No external Lean build or
named axiom audit has yet been recorded for this source.
-/

noncomputable section

open Filter
open scoped Topology

namespace HVRNativeZetaPoleEquality

/-- Pointwise logarithmic-derivative factorization when the regularized zeta
factor is nonzero. -/
theorem log_derivative_eq {s : ℂ} (hs : s ≠ 1)
    (hreg : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs,
    riemannZeta_eq_inv_sub_mul hs]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsub, hreg]
  <;> ring

/-- The pointwise identity holds eventually in the punctured neighborhood of
the actual zeta pole. -/
theorem log_derivative_eventually_eq :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ),
      deriv riemannZeta s / riemannZeta s =
        - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  filter_upwards [self_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs hreg
  have hs' : s ≠ (1 : ℂ) := by simpa using hs
  exact log_derivative_eq hs' hreg

end HVRNativeZetaPoleEquality
