import SingularClosure.PeriodicSobolev

/-! Continuity and cancellation for the regularized cubic dual mass. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology

namespace SingularClosure
noncomputable section

theorem critical_cubic_mass_polynomial (u : Vec → ℂ) (hu : Continuous u) (δ : ℝ) :
    (∫ x in unitCube, (‖u x‖ + δ) ^ 3) =
      (∫ x in unitCube, ‖u x‖ ^ 3) +
        (3 * δ) * (∫ x in unitCube, ‖u x‖ ^ 2) +
        ((3 * δ ^ 2) * (∫ x in unitCube, ‖u x‖) +
          δ ^ 3 * (∫ _x : Vec in unitCube, (1 : ℝ))) := by
  have h1 : IntegrableOn (fun x => ‖u x‖) unitCube volume :=
    hu.norm.continuousOn.integrableOn_compact isCompact_unitCube
  have h2 : IntegrableOn (fun x => ‖u x‖ ^ 2) unitCube volume :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have h3 : IntegrableOn (fun x => ‖u x‖ ^ 3) unitCube volume :=
    (hu.norm.pow 3).continuousOn.integrableOn_compact isCompact_unitCube
  have hc : IntegrableOn (fun _x : Vec => (1 : ℝ)) unitCube volume :=
    continuous_const.continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube,
        (‖u x‖ ^ 3 + (3 * δ) * ‖u x‖ ^ 2) +
          ((3 * δ ^ 2) * ‖u x‖ + δ ^ 3 * 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = _ := by
      have hout := integral_add (h3.add (h2.const_mul (3 * δ)))
        ((h1.const_mul (3 * δ ^ 2)).add (hc.const_mul (δ ^ 3)))
      have hleft := integral_add h3 (h2.const_mul (3 * δ))
      have hright := integral_add (h1.const_mul (3 * δ ^ 2)) (hc.const_mul (δ ^ 3))
      simp only [Pi.add_apply] at hout hleft hright
      rw [hout, hleft, hright, integral_const_mul, integral_const_mul, integral_const_mul]

theorem critical_cubic_mass_continuous (u : Vec → ℂ) (hu : Continuous u) :
    Continuous (fun δ : ℝ => ∫ x in unitCube, (‖u x‖ + δ) ^ 3) := by
  simp_rw [critical_cubic_mass_polynomial u hu]
  fun_prop

theorem critical_cubic_mass_cancel (u : Vec → ℂ) (hu : Continuous u)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ δ : ℝ, 0 < δ →
      (∫ x in unitCube, ‖u x‖ ^ 3) ≤
        K * (∫ x in unitCube, (‖u x‖ + δ) ^ 3) ^ (2 / 3 : ℝ)) :
    (∫ x in unitCube, ‖u x‖ ^ 3) ^ (1 / 3 : ℝ) ≤ K := by
  let I : ℝ := ∫ x in unitCube, ‖u x‖ ^ 3
  have hI : 0 ≤ I := integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _)
  have hcont : Continuous (fun δ : ℝ =>
      K * (∫ x in unitCube, (‖u x‖ + δ) ^ 3) ^ (2 / 3 : ℝ)) :=
    continuous_const.mul ((Real.continuous_rpow_const (by norm_num)).comp
      (critical_cubic_mass_continuous u hu))
  have ht : Tendsto (fun δ : ℝ =>
      K * (∫ x in unitCube, (‖u x‖ + δ) ^ 3) ^ (2 / 3 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (K * I ^ (2 / 3 : ℝ))) := by
    simpa only [add_zero, I] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      I ≤ K * (∫ x in unitCube, (‖u x‖ + δ) ^ 3) ^ (2 / 3 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hbound δ hδ
  have hlim : I ≤ K * I ^ (2 / 3 : ℝ) := ge_of_tendsto ht he
  by_cases hz : I = 0
  · change I ^ (1 / 3 : ℝ) ≤ K
    simpa only [hz, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using hK
  · have hpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hz)
    have hp : 0 < I ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hpos _
    have heq : I ^ (1 / 3 : ℝ) * I ^ (2 / 3 : ℝ) = I := by
      rw [← Real.rpow_add hpos]
      norm_num
    change I ^ (1 / 3 : ℝ) ≤ K
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      I ^ (1 / 3 : ℝ) * I ^ (2 / 3 : ℝ) = I := heq
      _ ≤ K * I ^ (2 / 3 : ℝ) := hlim

end
end SingularClosure
