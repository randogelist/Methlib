import QuasiFeffermanB.CaloricFrequencyGeometry

/-! Exact sharp Euclidean bound for the actual finite Galerkin nonlinearity. -/

set_option autoImplicit false
set_option Elab.async true
noncomputable section
open SingularClosure
open scoped BigOperators

namespace QuasiFeffermanB

theorem COEFFICIENT_TRANSPORT_SHARP_EUCLIDEAN
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ i : Fin 3, c p i = 0)
    (hsol : SpectralSolenoidal c) (k : Frequency) (hk : k ≠ 0) :
    complexVecNorm (coefficientLeray k (coefficientTransport N c k)) ≤
      (criticalFrequencyWeight k / 2) *
        ∑ p ∈ cutoffModes N, complexVecNorm (c p) * complexVecNorm (c (k - p)) := by
  let F : Frequency → Fin 3 → ℂ := fun p =>
    coefficientLeray k (symmetricFrequencyTensor k (c p) (c (k - p)))
  have hnorm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
    simp [norm_mul, Real.norm_eq_abs, Real.pi_pos.le]
  have heval : ((Real.pi : ℂ) * Complex.I) • (∑ p ∈ cutoffModes N, F p) =
      fun i => ((Real.pi : ℂ) * Complex.I) * (∑ p ∈ cutoffModes N, F p i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  calc
    complexVecNorm (coefficientLeray k (coefficientTransport N c k)) =
        Real.pi * complexVecNorm (fun i => ∑ p ∈ cutoffModes N, F p i) := by
      rw [coefficientLeray_transport_symmetric N c hsupp hsol k]
      change complexVecNorm (((Real.pi : ℂ) * Complex.I) • (∑ p ∈ cutoffModes N, F p)) = _
      rw [heval, complexVecNorm_smul, hnorm]
    _ ≤ Real.pi * ∑ p ∈ cutoffModes N, complexVecNorm (F p) :=
      mul_le_mul_of_nonneg_left (complexVecNorm_finset_sum_le (cutoffModes N) F) Real.pi_pos.le
    _ ≤ Real.pi * ∑ p ∈ cutoffModes N,
        Real.sqrt (galerkinFreqSq k : ℝ) *
          (complexVecNorm (c p) * complexVecNorm (c (k - p))) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply Finset.sum_le_sum
      intro p _
      exact coefficientLeray_symmetric_frequency_bound k hk (c p) (c (k - p))
    _ = (criticalFrequencyWeight k / 2) *
        ∑ p ∈ cutoffModes N, complexVecNorm (c p) * complexVecNorm (c (k - p)) := by
      rw [← Finset.mul_sum, criticalFrequencyWeight_eq_two_pi_radius k hk]
      ring

end QuasiFeffermanB
