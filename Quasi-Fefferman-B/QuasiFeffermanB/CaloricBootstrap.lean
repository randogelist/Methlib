import QuasiFeffermanB.CaloricFiniteNorm
import QuasiFeffermanB.CaloricBarrier

/-! The finite caloric scalar bootstrap with the exact symmetric coefficient
1/(2 sqrt(2ν)). All inputs are pointwise finite Duhamel estimates. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace QuasiFeffermanB
noncomputable section

theorem FINITE_CALORIC_QUADRATIC_ESTIMATE
    {ι : Type*} (s : Finset ι) (κ : ι → ℝ)
    (ν T H : ℝ) (hν : 0 < ν) (hT : 0 ≤ T) (hκ : ∀ i ∈ s, 0 < κ i)
    (A h : ℝ → ℝ) (f : ι → ℝ → ℝ)
    (hAc : ContinuousOn A (Icc 0 T)) (hhc : ContinuousOn h (Icc 0 T))
    (hfc : ∀ i ∈ s, ContinuousOn (f i) (Icc 0 T))
    (hA0 : ∀ t ∈ Icc 0 T, 0 ≤ A t) (hh0 : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hf0 : ∀ i ∈ s, ∀ t ∈ Icc 0 T, 0 ≤ f i t)
    (hpoint : ∀ t ∈ Icc 0 T,
      A t ≤ h t + (1 / 2 : ℝ) * ∑ i ∈ s, caloricVolterra ν (κ i) (f i) t)
    (hsource : ∀ t ∈ Icc 0 T, (∑ i ∈ s, f i t) ≤ A t ^ 2)
    (hheat : finiteTimeL2 T h ≤ H) :
    finiteTimeL2 T A ≤ H + (1 / (2 * Real.sqrt (2 * ν))) * finiteTimeL2 T A ^ 2 := by
  let y : ι → ℝ → ℝ := fun i => caloricVolterra ν (κ i) (f i)
  have hyc (i : ι) (hi : i ∈ s) : ContinuousOn (y i) (Icc 0 T) :=
    caloricVolterra_continuousOn ν (κ i) T (f i) hT (hfc i hi)
  have hy0 (i : ι) (hi : i ∈ s) (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ y i t :=
    (caloricVolterra_nonneg_le_primitive ν (κ i) T (f i) hν.le (hκ i hi).le hT
      (hfc i hi) (hf0 i hi) t ht).1
  have hsumc : ContinuousOn (fun t => ∑ i ∈ s, y i t) (Icc 0 T) :=
    continuousOn_finsetSum s hyc
  have hsum0 (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ ∑ i ∈ s, y i t :=
    Finset.sum_nonneg (fun i hi => hy0 i hi t ht)
  have hiF : (∑ i ∈ s, ∫ t in (0 : ℝ)..T, f i t) ≤
      finiteTimeL2 T A ^ 2 := by
    rw [finiteTimeL2_sq T hT, ← intervalIntegral.integral_finsetSum
      (fun i hi => (hfc i hi).intervalIntegrable_of_Icc hT)]
    exact intervalIntegral.integral_mono_on hT
      ((continuousOn_finsetSum s hfc).intervalIntegrable_of_Icc hT)
      ((hAc.pow 2).intervalIntegrable_of_Icc hT) hsource
  have hY : finiteTimeL2 T (fun t => ∑ i ∈ s, y i t) ≤
      finiteTimeL2 T A ^ 2 / Real.sqrt (2 * ν) := by
    calc
      _ ≤ ∑ i ∈ s, finiteTimeL2 T (y i) := finiteTimeL2_sum_le s T hT y hyc hy0
      _ ≤ ∑ i ∈ s, (∫ t in (0 : ℝ)..T, f i t) / Real.sqrt (2 * ν) := by
        apply Finset.sum_le_sum
        intro i hi
        exact CALORIC_VOLTERRA_L2_BOUND ν (κ i) T (f i) hν (hκ i hi) hT (hfc i hi) (hf0 i hi)
      _ = (∑ i ∈ s, ∫ t in (0 : ℝ)..T, f i t) / Real.sqrt (2 * ν) :=
        (Finset.sum_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right hiF (Real.sqrt_nonneg _)
  calc
    _ ≤ finiteTimeL2 T (fun t => h t + (1 / 2 : ℝ) * ∑ i ∈ s, y i t) :=
      finiteTimeL2_mono T hT A _ hAc (hhc.add (hsumc.const_mul _)) hA0 hpoint
    _ ≤ finiteTimeL2 T h + finiteTimeL2 T (fun t => (1 / 2 : ℝ) * ∑ i ∈ s, y i t) :=
      finiteTimeL2_add_le T hT h _ hhc (hsumc.const_mul _) hh0
        (fun t ht => mul_nonneg (by norm_num) (hsum0 t ht))
    _ = finiteTimeL2 T h + (1 / 2 : ℝ) * finiteTimeL2 T (fun t => ∑ i ∈ s, y i t) := by
      rw [finiteTimeL2_const_mul T (1 / 2) hT (by norm_num)]
    _ ≤ H + (1 / 2 : ℝ) * (finiteTimeL2 T A ^ 2 / Real.sqrt (2 * ν)) :=
      add_le_add hheat (mul_le_mul_of_nonneg_left hY (by norm_num))
    _ = _ := by ring

theorem finiteTimeL2_continuousOn_horizon
    (A : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T)) :
    ContinuousOn (fun t => finiteTimeL2 t A) (Icc 0 T) :=
  Real.continuous_sqrt.comp_continuousOn
    (caloric_primitive_continuousOn hT (hA.pow 2))

/-- The pointwise finite quadratic estimate gives one uniform actual time
integral budget on every horizon, including the zero heat-orbit case. -/
theorem FINITE_CALORIC_UNIFORM_BUDGET
    (ν H : ℝ) (hν : 0 < ν) (hH : 0 ≤ H)
    (hsmall : 4 * (1 / (2 * Real.sqrt (2 * ν))) * H < 1)
    (A : ℝ → ℝ) (hA : ContinuousOn A (Ici 0))
    (hquad : ∀ T : ℝ, 0 ≤ T →
      finiteTimeL2 T A ≤ H + (1 / (2 * Real.sqrt (2 * ν))) * finiteTimeL2 T A ^ 2) :
    ∀ T : ℝ, 0 ≤ T → (∫ t in (0 : ℝ)..T, A t ^ 2) ≤ 4 * H ^ 2 := by
  intro T hT
  have hb : 0 < 1 / (2 * Real.sqrt (2 * ν)) := by positivity
  have h := QUADRATIC_BARRIER_SQUARE_BUDGET
    (fun t => finiteTimeL2 t A) H (1 / (2 * Real.sqrt (2 * ν))) T hH hb hsmall
    (finiteTimeL2_continuousOn_horizon A T hT (hA.mono (fun t ht => ht.1)))
    (by simp [finiteTimeL2]) (fun t _ => finiteTimeL2_nonneg t A)
    (fun t ht => hquad t ht.1) T ⟨hT, le_rfl⟩
  rwa [finiteTimeL2_sq T hT] at h

end
end QuasiFeffermanB
