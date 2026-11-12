import QuasiFeffermanB.CaloricKernel
import QuasiFeffermanB.CaloricMultiplier
import QuasiFeffermanB.ThetaSchur
import QuasiFeffermanB.ThetaResolvent
import SingularClosure.CriticalInitialEnergy

/-! Exact finite caloric-to-critical estimate on actual unit-torus modes. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

private theorem cutoff_critical_weight_sqrt {N : ℕ} {k : Frequency}
    (hk : k ∈ cutoffModes N) :
    criticalFrequencyWeight k = 2 * Real.pi * Real.sqrt (galerkinFreqSq k : ℝ) := by
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  rw [criticalFrequencyWeight, if_neg hk0]
  unfold laplacianFrequency
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- Exact finite Schur estimate for arbitrary real scalar Fourier magnitudes.
The diagonal weighted test uses w(k)=1/|k|² directly. -/
theorem FINITE_CALORIC_SCHUR_SCALAR (N : ℕ) (a : Frequency → ℝ) :
    finiteCaloricQuadratic (cutoffModes N) criticalFrequencyWeight a ≤
      (∑ k ∈ cutoffModes N, criticalFrequencyWeight k * a k ^ 2) / (4 * Real.pi) := by
  let b : Frequency → ℝ := fun k => (galerkinFreqSq k : ℝ)
  let M : Frequency → Frequency → ℝ := fun k l =>
    1 / (criticalFrequencyWeight k ^ 2 + criticalFrequencyWeight l ^ 2)
  let w : Frequency → ℝ := fun k => 1 / b k
  let d : Frequency → ℝ := fun k => Real.sqrt (b k) / 2
  have hb : ∀ k ∈ cutoffModes N, 0 < b k := fun k hk => cutoff_frequency_square_pos hk
  have hκ : ∀ k ∈ cutoffModes N, criticalFrequencyWeight k ^ 2 = 4 * Real.pi ^ 2 * b k := by
    intro k hk
    rw [criticalFrequencyWeight_sq_of_ne_zero k ((mem_cutoffModes_iff N k).mp hk).2.1]
    unfold laplacianFrequency b
    ring
  have hM : ∀ k ∈ cutoffModes N, ∀ l ∈ cutoffModes N, 0 ≤ M k l := by
    intro k hk l hl
    exact one_div_nonneg.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsym : ∀ k ∈ cutoffModes N, ∀ l ∈ cutoffModes N, M k l = M l k := by
    intro k hk l hl
    dsimp [M]
    rw [add_comm]
  have hw : ∀ k ∈ cutoffModes N, 0 < w k := by
    intro k hk
    exact one_div_pos.mpr (hb k hk)
  have hrow : ∀ k ∈ cutoffModes N,
      (∑ l ∈ cutoffModes N, M k l * w l) ≤ d k * w k := by
    intro k hk
    let r : ℝ := Real.sqrt (b k)
    have hr : 0 < r := Real.sqrt_pos.mpr (hb k hk)
    have hrsq : r ^ 2 = b k := Real.sq_sqrt (hb k hk).le
    have hrowsum : (∑ l ∈ cutoffModes N, M k l * w l) =
        (1 / (4 * Real.pi ^ 2)) *
          ∑ l ∈ cutoffModes N, 1 / (b l * (r ^ 2 + b l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      dsimp [M, w]
      rw [hκ k hk, hκ l hl, hrsq]
      rw [show 4 * Real.pi ^ 2 * b k + 4 * Real.pi ^ 2 * b l =
        4 * Real.pi ^ 2 * (b k + b l) by ring]
      field_simp [Real.pi_ne_zero, ne_of_gt (hb l hl), ne_of_gt (add_pos (hb k hk) (hb l hl))]
      <;> ring
    calc
      (∑ l ∈ cutoffModes N, M k l * w l) =
          (1 / (4 * Real.pi ^ 2)) *
            ∑ l ∈ cutoffModes N, 1 / (b l * (r ^ 2 + b l)) := hrowsum
      _ ≤ (1 / (4 * Real.pi ^ 2)) * (2 * Real.pi ^ 2 / r) :=
        mul_le_mul_of_nonneg_left (FINITE_LATTICE_RESOLVENT_BOUND N r hr) (by positivity)
      _ = d k * w k := by
        change (1 / (4 * Real.pi ^ 2)) * (2 * Real.pi ^ 2 / r) = (r / 2) * (1 / b k)
        rw [← hrsq]
        field_simp [Real.pi_ne_zero, ne_of_gt hr]
        <;> ring
  have hschur := FINITE_WEIGHTED_SCHUR_DIAGONAL (cutoffModes N) M w a d hM hsym hw hrow
  have hleft : (∑ k ∈ cutoffModes N, ∑ l ∈ cutoffModes N, M k l * a k * a l) =
      finiteCaloricQuadratic (cutoffModes N) criticalFrequencyWeight a := by
    unfold finiteCaloricQuadratic
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [M]
    ring
  have hright : (∑ k ∈ cutoffModes N, d k * a k ^ 2) =
      (∑ k ∈ cutoffModes N, criticalFrequencyWeight k * a k ^ 2) / (4 * Real.pi) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [cutoff_critical_weight_sqrt hk]
    dsimp [d, b]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rwa [hleft, hright] at hschur

/-- Exact finite caloric estimate in the concrete Hermitian coefficient norm.
No smallness, reality, or solenoidal premise is needed for this embedding. -/
theorem FINITE_CALORIC_SCHUR (N : ℕ) (c : FourierCoeff) :
    finiteCaloricQuadratic (cutoffModes N) criticalFrequencyWeight
      (fun k => complexVecNorm (c k)) ≤ criticalEnergy 1 N c / (4 * Real.pi) := by
  have h := FINITE_CALORIC_SCHUR_SCALAR N (fun k => complexVecNorm (c k))
  have heq : (∑ k ∈ cutoffModes N, criticalFrequencyWeight k * complexVecNorm (c k) ^ 2) =
      criticalEnergy 1 N c := by
    unfold criticalEnergy
    apply Finset.sum_congr rfl
    intro k hk
    rw [complexVecNorm_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pow_one, Complex.normSq_eq_norm_sq]
  rwa [heq] at h

/-- The finite heat quadratic form is bounded by the actual homogeneous
H^(1/2) datum norm with the exact constant 1/(4π). -/
theorem CRITICAL_DATUM_FINITE_CALORIC_SCHUR (N : ℕ) (a : CriticalSobolev 1) :
    finiteCaloricQuadratic (cutoffModes N) criticalFrequencyWeight
      (fun k => complexVecNorm (criticalCoeff 1 a k)) ≤ ‖a‖ ^ 2 / (4 * Real.pi) := by
  exact (FINITE_CALORIC_SCHUR N (criticalCoeff 1 a)).trans
    (div_le_div_of_nonneg_right (criticalEnergy_le_norm_sq 1 N a) (by positivity))

end
end QuasiFeffermanB
