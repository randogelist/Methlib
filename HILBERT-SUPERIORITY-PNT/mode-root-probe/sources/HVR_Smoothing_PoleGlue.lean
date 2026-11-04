import HVR_Smoothing_AnalyticGerms

noncomputable section
open Filter
open scoped Topology

namespace HVRSmoothingAnalyticGerms

/-- The pole-regularized expression agrees with the raw expression in a
punctured neighborhood of zero. -/
theorem poleRegularPart_eventuallyEq_raw :
    (fun z : ℂ => poleRegularPart z) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => regularPartAt (1 + z)) := by
  have hshift : Tendsto (fun z : ℂ => 1 + z) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 + z) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpunct : Tendsto (fun z : ℂ => 1 + z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hshift
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro heq
      apply hz
      simpa only [add_eq_left] using heq
  have hlog := hpunct.eventually log_deriv_riemannZeta_eq_neg_inv_sub_add
  have hzeta1 := hshift.eventually riemannZeta₁_ne_zero_of_near_one
  have hnear : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), 1 + z ≠ 0 := by
    have hne : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), z ≠ 0 :=
      continuousAt_id.eventually_ne (show (1 : ℂ) ≠ 0 by norm_num)
    exact hshift.eventually hne
  filter_upwards [hlog, hnear, hzeta1, self_mem_nhdsWithin] with z hl hd hzeta hz
  have hz0 : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  change deriv riemannZeta (1 + z) / riemannZeta (1 + z) =
    -((1 + z) - 1)⁻¹ + deriv riemannZeta₁ (1 + z) / riemannZeta₁ (1 + z) at hl
  unfold poleRegularPart regularPartAt
  simp only [neg_div]
  rw [hl]
  have heq : (1 : ℂ) + z - 1 = z := by ring
  rw [heq]
  field_simp [hz0, hd, hzeta]
  <;> ring


end HVRSmoothingAnalyticGerms
