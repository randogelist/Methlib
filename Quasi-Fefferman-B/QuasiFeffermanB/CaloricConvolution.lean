import Mathlib

/-! Exact finite-horizon L1-to-L2 bound for a differentiated heat mode.
The proof uses the scalar ODE energy identity, avoiding an abstract Young
inequality and any infinite Fourier summation. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval

namespace QuasiFeffermanB
noncomputable section

theorem caloric_primitive_continuousOn
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
  simpa only [uIcc_of_le hT] using
    (intervalIntegral.continuousOn_primitive_interval'
      (hf.intervalIntegrable_of_Icc hT) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T))

theorem caloric_primitive_hasDerivAt
    {f : ℝ → ℝ} {T t : ℝ} (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, f s) (f t) t := by
  have hi : IntervalIntegrable f volume 0 t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter f (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

def caloricVolterra (ν κ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-ν * κ ^ 2 * t) *
    ∫ s in (0 : ℝ)..t, κ * Real.exp (ν * κ ^ 2 * s) * f s

theorem caloricVolterra_kernel (ν κ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    caloricVolterra ν κ f t =
      ∫ s in (0 : ℝ)..t, κ * Real.exp (-ν * κ ^ 2 * (t - s)) * f s := by
  rw [caloricVolterra, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  calc
    _ = κ * (Real.exp (-ν * κ ^ 2 * t) * Real.exp (ν * κ ^ 2 * s)) * f s := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

theorem caloricVolterra_continuousOn
    (ν κ T : ℝ) (f : ℝ → ℝ) (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (caloricVolterra ν κ f) (Icc 0 T) := by
  have he : Continuous (fun t : ℝ => Real.exp (-ν * κ ^ 2 * t)) := by fun_prop
  have hi : ContinuousOn (fun s : ℝ => κ * Real.exp (ν * κ ^ 2 * s) * f s) (Icc 0 T) := by
    exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn).mul hf
  exact he.continuousOn.mul (caloric_primitive_continuousOn hT hi)

theorem caloricVolterra_hasDerivAt
    (ν κ T : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (caloricVolterra ν κ f)
      (κ * f t - ν * κ ^ 2 * caloricVolterra ν κ f t) t := by
  have hi : ContinuousOn (fun s : ℝ => κ * Real.exp (ν * κ ^ 2 * s) * f s) (Icc 0 T) :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn).mul hf
  have hp := caloric_primitive_hasDerivAt hi ht
  have he := ((hasDerivAt_id t).const_mul (-ν * κ ^ 2)).exp
  have hexp : Real.exp (-ν * κ ^ 2 * t) * Real.exp (ν * κ ^ 2 * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  convert he.mul hp using 1 <;> dsimp only [caloricVolterra]
  linear_combination -(κ * f t) * hexp

theorem caloricVolterra_nonneg_le_primitive
    (ν κ T : ℝ) (f : ℝ → ℝ) (hν : 0 ≤ ν) (hκ : 0 ≤ κ)
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    0 ≤ caloricVolterra ν κ f t ∧
      caloricVolterra ν κ f t ≤ κ * ∫ s in (0 : ℝ)..t, f s := by
  have hfi : IntervalIntegrable f volume 0 t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hc : Continuous (fun s : ℝ => κ * Real.exp (-ν * κ ^ 2 * (t - s))) := by fun_prop
  have hki : IntervalIntegrable
      (fun s => κ * Real.exp (-ν * κ ^ 2 * (t - s)) * f s) volume 0 t :=
    (hc.continuousOn.mul (hf.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  rw [caloricVolterra_kernel]
  constructor
  · apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact mul_nonneg (mul_nonneg hκ (Real.exp_pos _).le) (hf0 s ⟨hs.1, hs.2.trans ht.2⟩)
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ht.1 hki (hfi.const_mul κ)
    intro s hs
    have he : Real.exp (-ν * κ ^ 2 * (t - s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hh := mul_nonneg (mul_nonneg hν (sq_nonneg κ)) (sub_nonneg.mpr hs.2)
      nlinarith
    have hn := hf0 s ⟨hs.1, hs.2.trans ht.2⟩
    nlinarith [mul_le_mul_of_nonneg_left he hκ,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hκ) hn]

/-- Exact sharp kernel constant, proved through the literal scalar heat ODE. -/
theorem CALORIC_VOLTERRA_L2_SQUARE_BOUND
    (ν κ T : ℝ) (f : ℝ → ℝ) (hν : 0 < ν) (hκ : 0 < κ)
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc 0 T))
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) :
    (∫ t in (0 : ℝ)..T, caloricVolterra ν κ f t ^ 2) ≤
      (∫ t in (0 : ℝ)..T, f t) ^ 2 / (2 * ν) := by
  let y := caloricVolterra ν κ f
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s
  let Z : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, y s ^ 2
  let E : ℝ → ℝ := fun t => y t ^ 2 + 2 * ν * κ ^ 2 * Z t - κ ^ 2 * F t ^ 2
  have hy : ContinuousOn y (Icc 0 T) := caloricVolterra_continuousOn ν κ T f hT hf
  have hF : ContinuousOn F (Icc 0 T) := caloric_primitive_continuousOn hT hf
  have hZ : ContinuousOn Z (Icc 0 T) := caloric_primitive_continuousOn hT (hy.pow 2)
  have hE : ContinuousOn E (Icc 0 T) :=
    ((hy.pow 2).add (hZ.const_mul _)).sub ((hF.pow 2).const_mul _)
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt E (2 * κ * f t * (y t - κ * F t)) t := by
    have hyd := caloricVolterra_hasDerivAt ν κ T f hf t ht
    have hFd := caloric_primitive_hasDerivAt hf ht
    have hZd := caloric_primitive_hasDerivAt (hy.pow 2) ht
    convert ((hyd.pow 2).add (hZd.const_mul (2 * ν * κ ^ 2))).sub
      ((hFd.pow 2).const_mul (κ ^ 2)) using 1 <;> dsimp only [E, y, F, Z] <;> ring
  have ha : AntitoneOn E (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hE
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      rw [(hd t ht').deriv]
      have hb := (caloricVolterra_nonneg_le_primitive ν κ T f hν.le hκ.le hT hf hf0
        t ⟨ht'.1.le, ht'.2.le⟩).2
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (by norm_num) hκ.le) (hf0 t ⟨ht'.1.le, ht'.2.le⟩))
        (sub_nonpos.mpr hb)
  have hend := ha ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have he0 : E 0 = 0 := by simp [E, F, Z, y, caloricVolterra]
  rw [he0] at hend
  have hκ2 : 0 < κ ^ 2 := sq_pos_of_pos hκ
  apply (le_div_iff₀ (mul_pos (by norm_num) hν)).2
  apply (mul_le_mul_left hκ2).mp
  dsimp only [E, Z, F] at hend
  nlinarith [sq_nonneg (y T)]

end
end QuasiFeffermanB
