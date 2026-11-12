import QuasiFeffermanB.CaloricGalerkinBudget
import QuasiFeffermanB.CaloricBootstrap
import QuasiFeffermanB.CaloricKernel
import QuasiFeffermanB.CaloricConstants
import QuasiFeffermanB.CaloricPhysicalControl

/-! Actual Galerkin mode norms, finite convolution counting, and the
pointwise-to-integrated caloric bound. The sharp finite Fourier estimate is
an explicit algebraic input to this assembly edge. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def finiteModeConvolution (N : ℕ) (c : FourierCoeff) (k : Frequency) : ℝ :=
  ∑ p ∈ cutoffModes N, complexVecNorm (c p) * complexVecNorm (c (k - p))

theorem finiteModeConvolution_nonneg (N : ℕ) (c : FourierCoeff) (k : Frequency) :
    0 ≤ finiteModeConvolution N c k :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (complexVecNorm_nonneg _) (complexVecNorm_nonneg _))

theorem FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k, k ∉ cutoffModes N → ∀ i, c k i = 0) :
    (∑ k ∈ cutoffModes N, finiteModeConvolution N c k) ≤ finiteChi0 (cutoffModes N) c ^ 2 := by
  have hs (k : Frequency) (hk : k ∉ cutoffModes N) : complexVecNorm (c k) = 0 := by
    have hc : c k = 0 := funext (hsupp k hk)
    simp [hc, complexVecNorm]
  simpa only [finiteModeConvolution, finiteChi0, pow_two] using
    FINITE_NONNEGATIVE_CONVOLUTION_L1 (cutoffModes N) (cutoffModes N) (cutoffModes N)
      (fun k => complexVecNorm (c k)) (fun k => complexVecNorm (c k))
      (fun k => complexVecNorm_nonneg _) (fun k => complexVecNorm_nonneg _) hs

theorem GALERKIN_MODE_CONVOLUTION_CONTINUOUS
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (k : Frequency) :
    ContinuousOn (fun t => finiteModeConvolution N (g.coeff t) k) (Ici 0) := by
  unfold finiteModeConvolution
  apply continuousOn_finset_sum
  intro p _
  simp_rw [complexVecNorm_eq_norm]
  exact (GALERKIN_COMPLEX_MODE_CONTINUOUS g p).norm.mul
    (GALERKIN_COMPLEX_MODE_CONTINUOUS g (k - p)).norm

theorem GALERKIN_MODE_DUHAMEL_NORM
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (hk : k ∈ cutoffModes N) (T : ℝ) (hT : 0 ≤ T) :
    complexVecNorm (g.coeff T k) ≤
      Real.exp (-(ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * T) *
        complexVecNorm (g.coeff 0 k) +
      ∫ s in (0 : ℝ)..T,
        Real.exp (-(ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * (T - s)) *
          complexVecNorm (coefficientLeray k (coefficientTransport N (g.coeff s) k)) := by
  rw [complexVecNorm_eq_norm, GALERKIN_MODE_DUHAMEL g k hk T hT]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simp only [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, complexVecNorm_eq_norm, le_refl]
  · have h := intervalIntegral.norm_integral_le_integral_norm (f := fun s =>
        Real.exp (-(ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * (T - s)) •
          (-complexVec (coefficientLeray k (coefficientTransport N (g.coeff s) k)))) hT
    simpa only [norm_smul, norm_neg, Real.norm_of_nonneg (Real.exp_pos _).le,
      complexVecNorm_eq_norm] using h

theorem GALERKIN_MODE_CALORIC_MAJORANT
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (hk : k ∈ cutoffModes N) (T : ℝ) (hT : 0 ≤ T)
    (hsharp : ∀ t : ℝ, 0 ≤ t →
      complexVecNorm (coefficientLeray k (coefficientTransport N (g.coeff t) k)) ≤
        (criticalFrequencyWeight k / 2) * finiteModeConvolution N (g.coeff t) k) :
    complexVecNorm (g.coeff T k) ≤
      Real.exp (-ν * criticalFrequencyWeight k ^ 2 * T) * complexVecNorm (g.coeff 0 k) +
        (1 / 2 : ℝ) * caloricVolterra ν (criticalFrequencyWeight k)
          (fun t => finiteModeConvolution N (g.coeff t) k) T := by
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  have hw : ν * criticalFrequencyWeight k ^ 2 =
      ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) := by
    rw [criticalFrequencyWeight_sq_of_ne_zero k hk0, laplacianFrequency]
    ring
  have hm := GALERKIN_MODE_DUHAMEL_NORM g k hk T hT
  rw [← hw] at hm
  simp only [neg_mul] at hm
  have hpc : ContinuousOn
      (fun s => complexVecNorm (coefficientLeray k (coefficientTransport N (g.coeff s) k))) (Icc 0 T) := by
    have h := (GALERKIN_COMPLEX_FORCING_CONTINUOUS g k hk).norm.mono (fun t ht => ht.1)
    simpa only [norm_neg, complexVecNorm_eq_norm] using h
  have hfc := (GALERKIN_MODE_CONVOLUTION_CONTINUOUS g k).mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun _ ht => ht.1)
  have he : Continuous (fun s : ℝ => Real.exp (-ν * criticalFrequencyWeight k ^ 2 * (T - s))) := by fun_prop
  apply hm.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∫ s in (0 : ℝ)..T, Real.exp (-ν * criticalFrequencyWeight k ^ 2 * (T - s)) *
        ((criticalFrequencyWeight k / 2) * finiteModeConvolution N (g.coeff s) k) := by
      apply intervalIntegral.integral_mono_on hT
        ((he.continuousOn.mul hpc).intervalIntegrable_of_Icc hT)
        ((he.continuousOn.mul (hfc.const_mul _)).intervalIntegrable_of_Icc hT)
      intro t ht
      exact mul_le_mul_of_nonneg_left (hsharp t ht.1) (Real.exp_pos _).le
    _ = (1 / 2 : ℝ) * caloricVolterra ν (criticalFrequencyWeight k)
        (fun t => finiteModeConvolution N (g.coeff t) k) T := by
      rw [caloricVolterra_kernel, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring

/-- Assembly of the sharp finite multiplier and actual heat-orbit norm.
The conclusion is the concrete χ0² budget used by caloric regularity. -/
theorem GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (hν : 0 < ν) (H : ℝ) (hH : 0 ≤ H)
    (hsmall : 4 * (1 / (2 * Real.sqrt (2 * ν))) * H < 1)
    (hsharp : ∀ k ∈ cutoffModes N, ∀ t : ℝ, 0 ≤ t →
      complexVecNorm (coefficientLeray k (coefficientTransport N (g.coeff t) k)) ≤
        (criticalFrequencyWeight k / 2) * finiteModeConvolution N (g.coeff t) k)
    (hheat : ∀ T : ℝ, 0 ≤ T → finiteTimeL2 T
      (finiteHeatSum (cutoffModes N) criticalFrequencyWeight
        (fun k => complexVecNorm (g.coeff 0 k)) ν) ≤ H) :
    ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ 4 * H ^ 2 := by
  apply FINITE_CALORIC_UNIFORM_BUDGET ν H hν hH hsmall
    (fun t => finiteChi0 (cutoffModes N) (g.coeff t)) (GALERKIN_CHI0_CONTINUOUS g)
  intro T hT
  let h : ℝ → ℝ := finiteHeatSum (cutoffModes N) criticalFrequencyWeight
    (fun k => complexVecNorm (g.coeff 0 k)) ν
  have hhc : ContinuousOn h (Icc 0 T) := by
    unfold h finiteHeatSum
    apply continuousOn_finset_sum
    intro k _
    fun_prop
  have hh0 (t : ℝ) (_ht : t ∈ Icc 0 T) : 0 ≤ h t := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (complexVecNorm_nonneg _) (Real.exp_pos _).le
  apply FINITE_CALORIC_QUADRATIC_ESTIMATE (cutoffModes N) criticalFrequencyWeight ν T H
    hν hT (fun k _ => criticalFrequencyWeight_pos k)
    (fun t => finiteChi0 (cutoffModes N) (g.coeff t)) h
    (fun k t => finiteModeConvolution N (g.coeff t) k)
    ((GALERKIN_CHI0_CONTINUOUS g).mono (fun t ht => ht.1)) hhc
    (fun k _ => (GALERKIN_MODE_CONVOLUTION_CONTINUOUS g k).mono (fun t ht => ht.1))
    (fun t _ => finiteChi0_nonneg _ _) hh0
    (fun k _ t _ => finiteModeConvolution_nonneg N (g.coeff t) k)
  · intro t ht
    calc
      finiteChi0 (cutoffModes N) (g.coeff t) ≤ ∑ k ∈ cutoffModes N,
          (Real.exp (-ν * criticalFrequencyWeight k ^ 2 * t) * complexVecNorm (g.coeff 0 k) +
            (1 / 2 : ℝ) * caloricVolterra ν (criticalFrequencyWeight k)
              (fun r => finiteModeConvolution N (g.coeff r) k) t) := by
        apply Finset.sum_le_sum
        intro k hk
        exact GALERKIN_MODE_CALORIC_MAJORANT g k hk t ht.1 (hsharp k hk)
      _ = h t + (1 / 2 : ℝ) * ∑ k ∈ cutoffModes N,
          caloricVolterra ν (criticalFrequencyWeight k)
            (fun r => finiteModeConvolution N (g.coeff r) k) t := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  · intro t ht
    exact FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE N (g.coeff t) (g.mode_support t ht.1)
  · exact hheat T hT

theorem FINITE_HEAT_L2_ON_INTERVAL_LE
    {ι : Type*} (s : Finset ι) (κ a : ι → ℝ) (ν T : ℝ)
    (hν : 0 < ν) (hT : 0 ≤ T) (hκ : ∀ i ∈ s, 0 < κ i) :
    finiteTimeL2 T (finiteHeatSum s κ a ν) ≤
      Real.sqrt (finiteCaloricQuadratic s κ a / ν) := by
  apply Real.sqrt_le_sqrt
  rw [intervalIntegral.integral_of_le hT]
  have h := integral_mono_measure
    (Measure.restrict_mono_set volume (show Ioc (0 : ℝ) T ⊆ Ioi 0 from fun _ ht => ht.1))
    (Filter.Eventually.of_forall (fun t => sq_nonneg (finiteHeatSum s κ a ν t)))
    (FINITE_HEAT_SQUARE_INTEGRABLE s κ a ν hν hκ)
  rw [FINITE_HEAT_SQUARE_INTEGRAL s κ a ν hν hκ] at h
  exact h

/-- Exact numerical caloric admission for a genuine finite trajectory. -/
theorem GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (hν : 0 < ν) (B : ℝ) (hB : 0 ≤ B) (hsmall : B < ν ^ 2 / 2)
    (hsharp : ∀ k ∈ cutoffModes N, ∀ t : ℝ, 0 ≤ t →
      complexVecNorm (coefficientLeray k (coefficientTransport N (g.coeff t) k)) ≤
        (criticalFrequencyWeight k / 2) * finiteModeConvolution N (g.coeff t) k)
    (hQ : finiteCaloricQuadratic (cutoffModes N) criticalFrequencyWeight
      (fun k => complexVecNorm (g.coeff 0 k)) ≤ B) :
    ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ 4 * B / ν := by
  have hs : 4 * (1 / (2 * Real.sqrt (2 * ν))) * caloricHeatBudget ν (Real.sqrt B) < 1 := by
    apply STRICT_CALORIC_DISCRIMINANT ν (Real.sqrt B) hν (Real.sqrt_nonneg B)
    simpa only [Real.sq_sqrt hB] using hsmall
  have hh (T : ℝ) (hT : 0 ≤ T) : finiteTimeL2 T
      (finiteHeatSum (cutoffModes N) criticalFrequencyWeight
        (fun k => complexVecNorm (g.coeff 0 k)) ν) ≤ caloricHeatBudget ν (Real.sqrt B) := by
    apply (FINITE_HEAT_L2_ON_INTERVAL_LE (cutoffModes N) criticalFrequencyWeight
      (fun k => complexVecNorm (g.coeff 0 k)) ν T hν hT
      (fun k _ => criticalFrequencyWeight_pos k)).trans
    have h := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hQ hν.le)
    simpa only [Real.sqrt_div hB ν, caloricHeatBudget] using h
  intro T hT
  have h := GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT g hν
    (caloricHeatBudget ν (Real.sqrt B)) (caloricHeatBudget_nonneg _ _ (Real.sqrt_nonneg B))
    hs hsharp hh T hT
  simpa only [caloricHeatBudget_sq ν (Real.sqrt B) hν, Real.sq_sqrt hB, mul_div_assoc] using h

end
end QuasiFeffermanB
