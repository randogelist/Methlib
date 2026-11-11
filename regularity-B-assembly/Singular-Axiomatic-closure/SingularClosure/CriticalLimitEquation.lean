import SingularClosure.FourierLimitEquation

/-! Actual Fourier integral equations for Galerkin families with varying initial cutoff data. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Interval Topology

namespace SingularClosure
noncomputable section

/-- Every actual compact-time H0 limit satisfies the untruncated modal integral equation. -/
theorem criticalGalerkinLimit_coefficient_integral
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν (a n) (φ n + 1))
    (T : ℝ) (hT : 0 ≤ T) (u : ℝ → TorusSobolev 0)
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    (u t).val k i = (u 0).val k i +
      ∫ r in (0 : ℝ)..t, fullFourierRhs ν (u r) k i := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hend := ((torusSobolevH0Coeff_continuous k i).tendsto (u t)).comp
    (hconv.tendsto_at ht)
  have hstart := ((torusSobolevH0Coeff_continuous k i).tendsto (u 0)).comp
    (hconv.tendsto_at hzero)
  by_cases hk : k = 0
  · subst k
    have hz (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : (u s).val 0 i = 0 := by
      have hlim := ((torusSobolevH0Coeff_continuous 0 i).tendsto (u s)).comp
        (hconv.tendsto_at hs)
      have hc : ∀ n : ℕ, ((g n).sobolevState 0 s).val 0 i = 0 := by
        intro n
        rw [(g n).sobolevState_coeff 0 hs.1]
        exact (g n).mode_support s hs.1 0 (cutoffModes_zero_not_mem _) i
      have hcconv : Tendsto (fun n : ℕ => ((g n).sobolevState 0 s).val 0 i)
          atTop (𝓝 0) := by
        simpa only [hc] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      exact tendsto_nhds_unique hlim hcconv
    simp only [hz t ht, hz 0 hzero, fullFourierRhs_zero_frequency,
      intervalIntegral.integral_zero, add_zero]
  · have hFc (n : ℕ) : ContinuousOn (fun r => (g n).sobolevState 0 r) (Icc 0 T) :=
      ((g n).sobolevState_continuousOn 0).mono (fun r hr => hr.1)
    have hR := fullFourierRhs_tendstoUniformlyOn ν k i T hFc hu hconv
    have hRsmall : TendstoUniformlyOn
        (fun n r => fullFourierRhs ν ((g n).sobolevState 0 r) k i)
        (fun r => fullFourierRhs ν (u r) k i) atTop (uIcc (0 : ℝ) t) := by
      rw [uIcc_of_le ht.1]
      exact hR.mono (Icc_subset_Icc le_rfl ht.2)
    have hcont : ∀ᶠ n : ℕ in atTop, ContinuousOn
        (fun r => fullFourierRhs ν ((g n).sobolevState 0 r) k i) (uIcc (0 : ℝ) t) := by
      apply Filter.Eventually.of_forall
      intro n
      rw [uIcc_of_le ht.1]
      exact (fullFourierRhs_continuous ν k i).comp_continuousOn
        (((g n).sobolevState_continuousOn 0).mono (fun r hr => hr.1))
    have hint := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (μ := (volume : Measure ℝ)) hcont hRsmall
    have heq : (fun n : ℕ =>
        ∫ r in (0 : ℝ)..t, fullFourierRhs ν ((g n).sobolevState 0 r) k i) =ᶠ[atTop]
          (fun n => ((g n).sobolevState 0 t).val k i -
            ((g n).sobolevState 0 0).val k i) := by
      filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
      exact (g n).coefficient_integral_fullFourierRhs hn i le_rfl ht.1
    have hid : (∫ r in (0 : ℝ)..t, fullFourierRhs ν (u r) k i) =
        (u t).val k i - (u 0).val k i :=
      tendsto_nhds_unique hint ((hend.sub hstart).congr' heq.symm)
    calc
      _ = (u 0).val k i + ((u t).val k i - (u 0).val k i) := by ring
      _ = _ := congrArg (fun z : ℂ => (u 0).val k i + z) hid.symm

/-- Global compact-time convergence gives the exact forward modal integral identity. -/
theorem criticalGalerkinGlobalLimit_coefficient_integral
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    (u t).val k i = (u 0).val k i +
      ∫ r in (0 : ℝ)..t, fullFourierRhs ν (u r) k i := by
  exact criticalGalerkinLimit_coefficient_integral ν a φ hφ g (t + 1) (by linarith) u
    (hu.mono (fun r hr => hr.1)) (hconv (t + 1) (by linarith))
    t ⟨ht, by linarith⟩ k i


end
end SingularClosure
