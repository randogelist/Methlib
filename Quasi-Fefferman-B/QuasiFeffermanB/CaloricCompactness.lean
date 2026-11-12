import QuasiFeffermanB.CaloricH2
import SingularClosure.CriticalTraceClosure
import SingularClosure.CriticalUniformBounds

/-! Genuine critical compactness from the caloric enstrophy/Laplacian bounds.
No critical-norm monotonicity and no numerical nonlinear smallness are used. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem caloric_criticalEnergy_le_succ (q N : ℕ) (c : FourierCoeff) :
    criticalEnergy q N c ≤ criticalEnergy (q + 1) N c := by
  unfold criticalEnergy
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  calc
    criticalFrequencyWeight k ^ q = criticalFrequencyWeight k ^ q * 1 := (mul_one _).symm
    _ ≤ criticalFrequencyWeight k ^ q * criticalFrequencyWeight k :=
      mul_le_mul_of_nonneg_left (criticalFrequencyWeight_one_le k)
        (pow_nonneg (criticalFrequencyWeight_pos k).le q)
    _ = _ := (pow_succ _ q).symm

theorem caloric_criticalEnergy_four_eq_laplacian (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 4 N c = coefficientLaplacianSquare N c := by
  unfold criticalEnergy coefficientLaplacianSquare
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  have hw : criticalFrequencyWeight k ^ 4 = laplacianFrequency k ^ 2 := by
    calc
      _ = (criticalFrequencyWeight k ^ 2) ^ 2 := by ring
      _ = _ := by rw [criticalFrequencyWeight_sq_of_ne_zero k hk0]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hw, laplacianFrequency]

theorem caloric_criticalEnergy_one_le_enstrophy (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 1 N c ≤ coefficientDissipation N c := by
  have h : criticalEnergy 1 N c ≤ criticalEnergy 2 N c :=
    caloric_criticalEnergy_le_succ 1 N c
  simpa only [criticalEnergy_two_eq_coefficientDissipation] using
    h

theorem caloric_criticalEnergy_three_le_laplacian (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 3 N c ≤ coefficientLaplacianSquare N c := by
  have h : criticalEnergy 3 N c ≤ criticalEnergy 4 N c :=
    caloric_criticalEnergy_le_succ 3 N c
  simpa only [caloric_criticalEnergy_four_eq_laplacian] using
    h

theorem GALERKIN_CRITICAL_RHS_SQUARE_OF_ENSTROPHY_BOUND
    {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (L : ℝ) (hL : 0 ≤ L)
    (t : ℝ) (ht : 0 ≤ t)
    (hD : coefficientDissipation N (g.coeff t) ≤ L) :
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * (L + 1)) ^ 2 *
        criticalEnergy 3 N (g.coeff t) := by
  have hE1 : criticalEnergy 1 N (g.coeff t) ≤ L :=
    (caloric_criticalEnergy_one_le_enstrophy N (g.coeff t)).trans hD
  have hsqrt : Real.sqrt (criticalEnergy 1 N (g.coeff t)) ≤ L + 1 := by
    have hsq := Real.sq_sqrt (criticalEnergy_nonneg 1 N (g.coeff t))
    nlinarith [Real.sqrt_nonneg (criticalEnergy 1 N (g.coeff t)),
      sq_nonneg (Real.sqrt (criticalEnergy 1 N (g.coeff t)) - 1)]
  have hE2 : criticalEnergy 2 N (g.coeff t) ≤
      (L + 1) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) :=
    (criticalEnergy_interpolation_sqrt N (g.coeff t)).trans
      (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))
  have hrhs : ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * (L + 1)) *
        Real.sqrt (criticalEnergy 3 N (g.coeff t)) := by
    rw [g.criticalRhs_eq_finiteSobolev (-1) t ht]
    calc
      _ ≤ ν * Real.sqrt (criticalEnergy 3 N (g.coeff t)) +
          criticalTransportConstant * criticalEnergy 2 N (g.coeff t) :=
        criticalFiniteSobolev_rhs_neg_one_bound ν hν N (g.coeff t)
          (g.mode_support t ht) (g.real_symmetry t ht)
      _ ≤ ν * Real.sqrt (criticalEnergy 3 N (g.coeff t)) +
          criticalTransportConstant * ((L + 1) *
            Real.sqrt (criticalEnergy 3 N (g.coeff t))) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hE2 criticalTransportConstant_pos.le)
      _ = _ := by ring
  have h := pow_le_pow_left₀ (norm_nonneg _) hrhs 2
  simpa only [mul_pow, Real.sq_sqrt (criticalEnergy_nonneg 3 N (g.coeff t))] using h

/-- Actual compactness and strong critical initial trace follow from the
enstrophy and integrated Laplacian bounds alone. -/
theorem GALERKIN_CRITICAL_COMPACTNESS_OF_ENSTROPHY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (n + 1) (criticalCoeff 1 a)) (n + 1))
    (L : ℝ) (hL : 0 ≤ L)
    (hD : ∀ n t, 0 ≤ t → coefficientDissipation (n + 1) ((g n).coeff t) ≤ L)
    (hZ : ∀ n T, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare (n + 1) ((g n).coeff t)) ≤ L / ν) :
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ L + 1) ∧
      (∀ T : ℝ, TendstoUniformlyOn (fun n t => (g (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) := by
  have hE3 (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in (0 : ℝ)..T, criticalEnergy 3 (n + 1) ((g n).coeff t)) ≤ L / ν := by
    apply le_trans _ (hZ n T hT)
    apply intervalIntegral.integral_mono_on hT
    · exact (((g n).criticalEnergy_continuousOn 3).mono
        (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
    · exact ((g n).coefficientLaplacianSquare_continuousOn.mono
        (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
    · intro t _
      exact caloric_criticalEnergy_three_le_laplacian (n + 1) ((g n).coeff t)
  apply CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE ν a hreal hzero g
    (L + 1) (L / ν) ((ν + criticalTransportConstant * (L + 1)) ^ 2 * (L / ν))
    (by linarith) (div_nonneg hL hν.le) (mul_nonneg (sq_nonneg _) (div_nonneg hL hν.le))
  · intro n t ht
    have hn : ‖(g n).criticalState 1 t‖ ^ 2 ≤ L := by
      rw [show ‖(g n).criticalState 1 t‖ ^ 2 = criticalEnergy 1 (n + 1) ((g n).coeff t) from
        (g n).criticalState_norm_sq_nat 1 t]
      exact (caloric_criticalEnergy_one_le_enstrophy (n + 1) ((g n).coeff t)).trans (hD n t ht)
    nlinarith [norm_nonneg ((g n).criticalState 1 t), sq_nonneg (‖(g n).criticalState 1 t‖ - 1)]
  · intro n T hT
    have heq (t : ℝ) : ‖(g n).criticalState 3 t‖ ^ 2 =
        criticalEnergy 3 (n + 1) ((g n).coeff t) := (g n).criticalState_norm_sq_nat 3 t
    simp_rw [heq]
    exact hE3 n T hT
  · intro n T hT
    have hRi : IntervalIntegrable (fun t => ‖(g n).criticalRhs (-1) t‖ ^ 2) volume 0 T :=
      ((((g n).criticalRhs_continuousOn (-1)).mono (fun t ht => ht.1)).norm.pow 2).intervalIntegrable_of_Icc hT
    have hEi : IntervalIntegrable (fun t => criticalEnergy 3 (n + 1) ((g n).coeff t)) volume 0 T :=
      (((g n).criticalEnergy_continuousOn 3).mono (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
    calc
      _ ≤ ∫ t in (0 : ℝ)..T,
          (ν + criticalTransportConstant * (L + 1)) ^ 2 *
            criticalEnergy 3 (n + 1) ((g n).coeff t) := by
        apply intervalIntegral.integral_mono_on hT hRi (hEi.const_mul _)
        intro t ht
        exact GALERKIN_CRITICAL_RHS_SQUARE_OF_ENSTROPHY_BOUND hν.le (g n) L hL t ht.1 (hD n t ht.1)
      _ = (ν + criticalTransportConstant * (L + 1)) ^ 2 *
          (∫ t in (0 : ℝ)..T, criticalEnergy 3 (n + 1) ((g n).coeff t)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hE3 n T hT) (sq_nonneg _)

end
end QuasiFeffermanB
