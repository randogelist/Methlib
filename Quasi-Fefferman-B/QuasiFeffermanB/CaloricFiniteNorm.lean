import QuasiFeffermanB.CaloricConvolution
import SingularClosure.CriticalTrace
import SingularClosure.HighOrderProduct

/-! Finite continuous L2-time inequalities and finite Fourier L1 convolution. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval BigOperators ENNReal

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def finiteTimeL2 (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ t in (0 : ℝ)..T, f t ^ 2)

theorem finiteTimeL2_nonneg (T : ℝ) (f : ℝ → ℝ) : 0 ≤ finiteTimeL2 T f := Real.sqrt_nonneg _

theorem finiteTimeL2_sq (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ) :
    finiteTimeL2 T f ^ 2 = ∫ t in (0 : ℝ)..T, f t ^ 2 :=
  Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _))

theorem caloric_continuous_memLp_two {f : ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) : MemLp f 2 (volume.restrict (Icc 0 T)) := by
  apply (memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)).mpr
  exact (hf.pow 2).integrableOn_compact isCompact_Icc

theorem finiteTimeL2_cauchy
    (T : ℝ) (hT : 0 ≤ T) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t) :
    (∫ t in (0 : ℝ)..T, f t * g t) ≤ finiteTimeL2 T f * finiteTimeL2 T g := by
  apply criticalTrace_integral_mul_le_sqrt hT
    (caloric_continuous_memLp_two hf) (caloric_continuous_memLp_two hg)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hf0 t ht
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hg0 t ht

theorem finiteTimeL2_mono
    (T : ℝ) (hT : 0 ≤ T) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hfg : ∀ t ∈ Icc 0 T, f t ≤ g t) :
    finiteTimeL2 T f ≤ finiteTimeL2 T g := by
  apply Real.sqrt_le_sqrt
  apply intervalIntegral.integral_mono_on hT
    ((hf.pow 2).intervalIntegrable_of_Icc hT) ((hg.pow 2).intervalIntegrable_of_Icc hT)
  intro t ht
  exact pow_le_pow_left₀ (hf0 t ht) (hfg t ht) 2

theorem finiteTimeL2_add_le
    (T : ℝ) (hT : 0 ≤ T) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t) :
    finiteTimeL2 T (fun t => f t + g t) ≤ finiteTimeL2 T f + finiteTimeL2 T g := by
  have hiF := (hf.pow 2).intervalIntegrable_of_Icc hT
  have hiG := (hg.pow 2).intervalIntegrable_of_Icc hT
  have hiFG := (hf.mul hg).intervalIntegrable_of_Icc hT
  have heq : (∫ t in (0 : ℝ)..T, (f t + g t) ^ 2) =
      (∫ t in (0 : ℝ)..T, f t ^ 2) +
        2 * (∫ t in (0 : ℝ)..T, f t * g t) +
          (∫ t in (0 : ℝ)..T, g t ^ 2) := by
    have hp (t : ℝ) : (f t + g t) ^ 2 = (f t ^ 2 + 2 * (f t * g t)) + g t ^ 2 := by ring
    simp_rw [hp]
    rw [intervalIntegral.integral_add (hiF.add (hiFG.const_mul 2)) hiG,
      intervalIntegral.integral_add hiF (hiFG.const_mul 2), intervalIntegral.integral_const_mul]
  apply (sq_le_sq₀ (finiteTimeL2_nonneg _ _)
    (add_nonneg (finiteTimeL2_nonneg _ _) (finiteTimeL2_nonneg _ _))).mp
  rw [finiteTimeL2_sq T hT, heq]
  have hCS := finiteTimeL2_cauchy T hT f g hf hg hf0 hg0
  nlinarith [finiteTimeL2_sq T hT f, finiteTimeL2_sq T hT g]

theorem finiteTimeL2_const_mul
    (T c : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c) (f : ℝ → ℝ) :
    finiteTimeL2 T (fun t => c * f t) = c * finiteTimeL2 T f := by
  unfold finiteTimeL2
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem finiteTimeL2_sum_le
    {ι : Type*} (s : Finset ι) (T : ℝ) (hT : 0 ≤ T) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Icc 0 T))
    (hf0 : ∀ i ∈ s, ∀ t ∈ Icc 0 T, 0 ≤ f i t) :
    finiteTimeL2 T (fun t => ∑ i ∈ s, f i t) ≤ ∑ i ∈ s, finiteTimeL2 T (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteTimeL2]
  | @insert i s hi ih =>
      have hfc : ContinuousOn (fun t => ∑ j ∈ s, f j t) (Icc 0 T) :=
        continuousOn_finset_sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hfn : ∀ t ∈ Icc 0 T, 0 ≤ ∑ j ∈ s, f j t :=
        fun t ht => Finset.sum_nonneg (fun j hj => hf0 j (Finset.mem_insert_of_mem hj) t ht)
      simp only [Finset.sum_insert hi]
      exact (finiteTimeL2_add_le T hT (f i) (fun t => ∑ j ∈ s, f j t)
        (hf i (Finset.mem_insert_self _ _)) hfc
        (hf0 i (Finset.mem_insert_self _ _)) hfn).trans
          (add_le_add le_rfl (ih
            (fun j hj => hf j (Finset.mem_insert_of_mem hj))
            (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))))

theorem CALORIC_VOLTERRA_L2_BOUND
    (ν κ T : ℝ) (f : ℝ → ℝ) (hν : 0 < ν) (hκ : 0 < κ)
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) :
    finiteTimeL2 T (caloricVolterra ν κ f) ≤
      (∫ t in (0 : ℝ)..T, f t) / Real.sqrt (2 * ν) := by
  have hF : 0 ≤ ∫ t in (0 : ℝ)..T, f t :=
    intervalIntegral.integral_nonneg hT hf0
  apply (sq_le_sq₀ (finiteTimeL2_nonneg _ _)
    (div_nonneg hF (Real.sqrt_nonneg _))).mp
  rw [finiteTimeL2_sq T hT, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ν)]
  exact CALORIC_VOLTERRA_L2_SQUARE_BOUND ν κ T f hν hκ hT hf hf0

theorem FINITE_NONNEGATIVE_CONVOLUTION_L1
    (r s t : Finset Frequency) (a b : Frequency → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hbsupp : ∀ k, k ∉ t → b k = 0) :
    (∑ k ∈ r, ∑ p ∈ s, a p * b (k - p)) ≤
      (∑ p ∈ s, a p) * ∑ q ∈ t, b q := by
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (ha p)
  exact finite_sum_comp_le_of_support r t b hb hbsupp
    (fun k => k - p) (frequency_sub_right_injective p)

end
end QuasiFeffermanB
