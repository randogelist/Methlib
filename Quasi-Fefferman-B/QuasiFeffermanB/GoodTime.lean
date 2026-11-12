import QuasiFeffermanB.CriticalTimeBudget

noncomputable section

open MeasureTheory Set

namespace QuasiFeffermanB

/-- Strict mean-value extraction retaining any specified full-measure
restart condition. The function is not evaluated at an arbitrary selected
time; the witness is chosen in the intersection with that condition. -/
theorem exists_good_time_of_integral_lt
    {f : ℝ → ℝ} {Good : ℝ → Prop} {T c : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c)
    (hf : Integrable f (criticalTimeMeasure T))
    (hgood : ∀ᵐ t ∂criticalTimeMeasure T, Good t)
    (hbudget : (∫ t, f t ∂criticalTimeMeasure T) < c * T) :
    ∃ t, 0 < t ∧ t < T ∧ Good t ∧ f t < c := by
  by_contra hnone
  have hlower : ∀ᵐ t ∂criticalTimeMeasure T, c ≤ f t := by
    have htime : ∀ᵐ t ∂criticalTimeMeasure T, t ∈ Ioo 0 T :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [htime, hgood] with t ht hg
    by_contra hnot
    exact hnone ⟨t, ht.1, ht.2, hg, lt_of_not_ge hnot⟩
  have hcomparison :
      (∫ _ : ℝ, c ∂criticalTimeMeasure T) ≤
        ∫ t, f t ∂criticalTimeMeasure T :=
    integral_mono_of_nonneg (ae_of_all _ (fun _ => hc)) hf hlower
  have hconstant : (∫ _ : ℝ, c ∂criticalTimeMeasure T) = c * T := by
    change (∫ _ : ℝ in Ioo 0 T, c ∂volume) = c * T
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioo, hT.le, mul_comm]
  rw [hconstant] at hcomparison
  exact (not_lt_of_ge hcomparison) hbudget

/-- The exact 8π² cutoff supplies strict room below the squared critical
threshold. No amplitude restriction and no replacement of < by ≤ occurs. -/
theorem fourthPower_budget_lt_threshold
    {M μ T : ℝ} (hμ : 0 < μ)
    (hcut : energyCutoff M μ < T) :
    M ^ 2 / (2 * μ) < (2 * Real.pi * μ ^ 2) ^ 2 * T := by
  have hden : 0 < 8 * Real.pi ^ 2 * μ ^ 5 := by positivity
  have hscaled : M ^ 2 < T * (8 * Real.pi ^ 2 * μ ^ 5) :=
    (div_lt_iff₀ hden).mp hcut
  apply (div_lt_iff₀ (show 0 < 2 * μ by positivity)).2
  have heq : (2 * Real.pi * μ ^ 2) ^ 2 * T * (2 * μ) =
      T * (8 * Real.pi ^ 2 * μ ^ 5) := by ring
  rw [heq]
  exact hscaled

/-- Strict good-time selection for the squared H^(1/2) readout.
M=||a||₂² yields T > ||a||₂⁴/(8π² μ⁵).
Every externally justified full-measure restart predicate is retained. -/
theorem exists_subcritical_good_time
    {critical : ℝ → ℝ} {Good : ℝ → Prop} {M μ T : ℝ}
    (hμ : 0 < μ)
    (hcut : energyCutoff M μ < T)
    (hcritical : Integrable (fun t => critical t ^ 2) (criticalTimeMeasure T))
    (hgood : ∀ᵐ t ∂criticalTimeMeasure T, Good t)
    (hbudget : (∫ t, critical t ^ 2 ∂criticalTimeMeasure T) ≤ M ^ 2 / (2 * μ)) :
    ∃ t, 0 < t ∧ t < T ∧ Good t ∧ critical t < 2 * Real.pi * μ ^ 2 := by
  have hT : 0 < T := lt_of_le_of_lt (energyCutoff_nonneg hμ) hcut
  obtain ⟨t, ht0, htT, hg, hsmall⟩ :=
    exists_good_time_of_integral_lt hT (sq_nonneg (2 * Real.pi * μ ^ 2))
      hcritical hgood (hbudget.trans_lt (fourthPower_budget_lt_threshold hμ hcut))
  refine ⟨t, ht0, htT, hg, ?_⟩
  have hthreshold : 0 < 2 * Real.pi * μ ^ 2 := by positivity
  nlinarith [sq_nonneg (critical t - 2 * Real.pi * μ ^ 2)]

/-- Q07 for the literal extended Fourier energy, with an arbitrary full-measure
good-time predicate. No finiteness or midpoint premise remains at this endpoint. -/
theorem LH_GOOD_SUBCRITICAL_TIME
    {ν : ℝ} {a : SingularClosure.CriticalPhysicalL2}
    {u : SingularClosure.Velocity} {G : WeakGradientTrajectory}
    {Good : ℝ → Prop} {T : ℝ}
    (hν : 0 < ν) (hu : SingularClosure.CriticalLerayHopf ν a u G)
    (hcut : cutoff a ν < T)
    (hgood : ∀ᵐ t ∂criticalTimeMeasure T, Good t) :
    ∃ t, 0 < t ∧ t < T ∧ Good t ∧
      SingularClosure.CriticalPhysicalH1 (u t) (G t) ∧
      physicalHalfEnergy (u t) < ENNReal.ofReal (2 * Real.pi * ν ^ 2) := by
  have hcut' : energyCutoff (‖a‖ ^ 2) ν < T := by
    have heq : energyCutoff (‖a‖ ^ 2) ν = cutoff a ν := by
      unfold energyCutoff cutoff
      ring
    rw [heq]
    exact hcut
  have hT : 0 < T := lt_of_le_of_lt (energyCutoff_nonneg hν) hcut'
  obtain ⟨hint, hbudget⟩ := LH_FOURTH_POWER_BUDGET hν hu hT
  have hbudget' :
      (∫ t, (physicalHalfEnergy (u t)).toReal ^ 2 ∂criticalTimeMeasure T) ≤
        (‖a‖ ^ 2) ^ 2 / (2 * ν) := by
    convert hbudget using 1 <;> ring
  have hgood' : ∀ᵐ t ∂criticalTimeMeasure T,
      Good t ∧ SingularClosure.CriticalPhysicalH1 (u t) (G t) := by
    have hH1 := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self
      (hu.spatial_H1 T hT)
    filter_upwards [hgood, hH1] with t hg hH1
    exact ⟨hg, hH1⟩
  obtain ⟨t, ht0, htT, hg, hsmall⟩ :=
    exists_subcritical_good_time hν hcut' hint hgood' hbudget'
  refine ⟨t, ht0, htT, hg.1, hg.2, ?_⟩
  rw [← ENNReal.ofReal_toReal (physicalH1_halfEnergy_ne_top hg.2)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hsmall

end QuasiFeffermanB

