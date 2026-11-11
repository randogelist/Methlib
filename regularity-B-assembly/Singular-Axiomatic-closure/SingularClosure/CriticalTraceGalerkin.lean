import SingularClosure.CriticalTracePrimitive
import SingularClosure.CriticalLimitEquation
import SingularClosure.CriticalGalerkin
import SingularClosure.CriticalGalerkinTrajectory

/-! Identification of the strong trace with the single global Galerkin limit. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Interval

namespace SingularClosure

noncomputable section

/-- Every weighted Galerkin state has the same limiting Fourier coordinates. -/
theorem criticalGalerkinLimit_criticalState_coeff_tendsto
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (T : ℝ)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (q : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    Tendsto (fun n => criticalCoeff q ((g n).criticalState q t) k i)
      atTop (𝓝 ((u t).val k i)) := by
  have h := (torusSobolevH0Coeff_continuous k i).continuousAt.tendsto.comp
    (hconv.tendsto_at ht)
  have heq (n : ℕ) : criticalCoeff q ((g n).criticalState q t) k i =
      ((g n).sobolevState 0 t).val k i := by
    rw [(g n).criticalState_coeff q ht.1, (g n).sobolevState_coeff 0 ht.1]
  simpa only [heq, Function.comp_def] using h

/-- Actual finite time derivatives converge modewise to the full Fourier RHS. -/
theorem criticalGalerkinLimit_criticalRhs_coeff_tendsto
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (T : ℝ)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (q : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    Tendsto (fun n => criticalCoeff q ((g n).criticalRhs q t) k i)
      atTop (𝓝 (fullFourierRhs ν (u t) k i)) := by
  by_cases hk : k = 0
  · subst k
    have hz (n : ℕ) : criticalCoeff q ((g n).criticalRhs q t) 0 i = 0 := by
      rw [(g n).criticalRhs_eq_finiteSobolev q t ht.1, criticalFiniteSobolev_coeff]
      simp only [cutoffCoeff, cutoffModes_zero_not_mem, if_false]
    simpa only [hz, fullFourierRhs_zero_frequency] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  · have h := (fullFourierRhs_continuous ν k i).continuousAt.tendsto.comp
      (hconv.tendsto_at ht)
    simp only [Function.comp_def] at h
    apply h.congr'
    filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
    change fullFourierRhs ν ((g n).sobolevState 0 t) k i =
      criticalCoeff q ((g n).criticalRhs q t) k i
    rw [(g n).criticalRhs_coeff q t ht.1 hn i, (g n).fullFourierRhs_eq t ht.1 k i]

/-- The actual rough cutoff initial data converge to the prescribed initial vector. -/
theorem criticalGalerkinGlobalLimit_initial
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) 1)) :
    u 0 = a := by
  apply criticalCoeff_injective 1
  funext k i
  have hlim := (torusSobolevH0Coeff_continuous k i).continuousAt.tendsto.comp
    (hconv.tendsto_at (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1))
  simp only [Function.comp_def] at hlim
  have hevent : ∀ᶠ n in atTop, ((g n).sobolevState 0 0).val k i = criticalCoeff 1 a k i := by
    by_cases hk : k = 0
    · subst k
      exact Filter.Eventually.of_forall fun n => by
        rw [(g n).sobolevState_coeff 0 le_rfl, criticalGalerkin_initial_coeff hreal (g n)]
        simp only [cutoffCoeff, cutoffModes_zero_not_mem, if_false, hzero i]
    · filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
      rw [(g n).sobolevState_coeff 0 le_rfl, criticalGalerkin_initial_coeff hreal (g n)]
      exact if_pos hn
  have h := tendsto_nhds_unique hlim
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => criticalCoeff 1 a k i) atTop
      (𝓝 (criticalCoeff 1 a k i))).congr' (hevent.mono fun n hn => hn.symm))
  simpa only [criticalToTorusH0_coeff] using h

/-- Modal integral evolution starts from the actual prescribed rough coefficient array. -/
theorem criticalGalerkinGlobalLimit_criticalCoeff_integral_initial
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    criticalCoeff 1 (u t) k i = criticalCoeff 1 a k i +
      ∫ τ in (0 : ℝ)..t,
        fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u τ)) k i := by
  have hinit := criticalGalerkinGlobalLimit_initial ν a hreal hzero φ hφ g u
    (hconv 1 (by norm_num))
  have h := criticalGalerkinGlobalLimit_coefficient_integral ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g
    (fun τ => criticalToTorusH0 1 (by norm_num) (u τ)) hu hconv t ht k i
  simpa only [criticalToTorusH0_coeff, hinit] using h

/-- The actual limit coefficients have the full Fourier RHS as right derivative. -/
theorem criticalGalerkinGlobalLimit_criticalCoeff_hasDerivWithinAt
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → CriticalSobolev 1)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun τ => criticalCoeff 1 (u τ) k i)
      (fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t)) k i) (Ici 0) t := by
  have h := fullFourierIntegral_hasDerivWithinAt ν
    (fun τ => criticalToTorusH0 1 (by norm_num) (u τ)) hu
    (criticalGalerkinGlobalLimit_coefficient_integral ν a φ hφ g
      (fun τ => criticalToTorusH0 1 (by norm_num) (u τ)) hu hconv) t ht k i
  simpa only [criticalToTorusH0_coeff] using h

theorem criticalTracePrimitiveCoeff_eq_complexIntegral
    (a : CriticalSobolev 1) (v : ℝ → CriticalSobolev (-1))
    (t : ℝ) (k : Frequency) (i : Fin 3)
    (hv : IntervalIntegrable (fun τ => criticalCoeff (-1) (v τ) k i) volume 0 t) :
    criticalTracePrimitiveCoeff a v t k i = criticalCoeff 1 a k i +
      ∫ τ in (0 : ℝ)..t, criticalCoeff (-1) (v τ) k i := by
  have hre : (∫ τ in (0 : ℝ)..t, (criticalCoeff (-1) (v τ) k i).re) =
      (∫ τ in (0 : ℝ)..t, criticalCoeff (-1) (v τ) k i).re :=
    Complex.reCLM.intervalIntegral_comp_comm hv
  have him : (∫ τ in (0 : ℝ)..t, (criticalCoeff (-1) (v τ) k i).im) =
      (∫ τ in (0 : ℝ)..t, criticalCoeff (-1) (v τ) k i).im :=
    Complex.imCLM.intervalIntegral_comp_comm hv
  apply Complex.ext <;> simp [criticalTracePrimitiveCoeff, hre, him]

/-- The a.e. derivative representative gives the same primitive at every time. -/
theorem criticalTracePrimitiveCoeff_eq_modal_path
    (ν : ℝ) (a : CriticalSobolev 1) (u : ℝ → CriticalSobolev 1)
    (v : ℝ → CriticalSobolev (-1)) {T : ℝ} (hT : 0 ≤ T)
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hvcoeff : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff (-1) (v t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t)))
    (hmodal : ∀ t ∈ Icc (0 : ℝ) T, ∀ k i,
      criticalCoeff 1 (u t) k i = criticalCoeff 1 a k i +
        ∫ τ in (0 : ℝ)..t,
          fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u τ)) k i) :
    ∀ t ∈ Icc (0 : ℝ) T, criticalTracePrimitiveCoeff a v t = criticalCoeff 1 (u t) := by
  intro t ht
  funext k i
  have hcoeff : MemLp (fun τ => criticalCoeff (-1) (v τ) k i) 2
      (volume.restrict (Icc (0 : ℝ) T)) := by
    simpa only [Function.comp_def, criticalSobolevCoeff_apply] using
      (criticalSobolevCoeff (-1) k i).comp_memLp' hv
  have hint : IntervalIntegrable (fun τ => criticalCoeff (-1) (v τ) k i) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
      (MemLp.integrable (by norm_num) hcoeff)
  have hints : IntervalIntegrable (fun τ => criticalCoeff (-1) (v τ) k i) volume 0 t := by
    apply hint.mono_set
    simp only [uIcc_of_le hT, uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  rw [criticalTracePrimitiveCoeff_eq_complexIntegral a v t k i hints, hmodal t ht k i]
  congr 1
  apply intervalIntegral.integral_congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mp
  have hae : ∀ᵐ τ ∂volume.restrict (uIoc (0 : ℝ) t),
      criticalCoeff (-1) (v τ) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u τ)) := by
    apply ae_restrict_of_ae_restrict_of_subset _ hvcoeff
    simp only [uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  exact hae.mono fun τ hτ => congrFun (congrFun hτ k) i

/-- Local L2 representatives identify a single global Hhalf path as strongly continuous. -/
theorem CRITICAL_GLOBAL_STRONG_TRACE_OF_MODAL_EVOLUTION
    (ν : ℝ) (a : CriticalSobolev 1) (u : ℝ → CriticalSobolev 1)
    (hmodal : ∀ t : ℝ, 0 ≤ t → ∀ k i,
      criticalCoeff 1 (u t) k i = criticalCoeff 1 a k i +
        ∫ τ in (0 : ℝ)..t,
          fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u τ)) k i)
    (hrep : ∀ T : ℝ, 0 < T → ∃ U : ℝ → CriticalSobolev 3,
      ∃ V : ℝ → CriticalSobolev (-1),
        MemLp U 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff 3 (U t) = criticalCoeff 1 (u t)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff (-1) (V t) =
            fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t)))) :
    ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a := by
  have hlocal : ∀ T : ℝ, 0 < T → ContinuousOn u (Icc (0 : ℝ) T) ∧ u 0 = a := by
    intro T hT
    obtain ⟨U, V, hU, hV, hUc, hVc⟩ := hrep T hT
    have hprimitive := criticalTracePrimitiveCoeff_eq_modal_path ν a u V hT.le hV hVc
      (fun t ht => hmodal t ht.1)
    have hevolution : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalTracePrimitiveCoeff a V t = criticalCoeff 3 (U t) := by
      filter_upwards [hUc, ae_restrict_mem measurableSet_Icc] with t ht htI
      exact (hprimitive t htI).trans ht.symm
    obtain ⟨w, hw, hw0, hwc, _⟩ :=
      CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION a U V hT hU hV hevolution
    have heq : EqOn u w (Icc (0 : ℝ) T) := by
      intro t ht
      apply criticalCoeff_injective 1
      exact (hprimitive t ht).symm.trans (hwc t ht).symm
    exact ⟨hw.congr heq, (heq 0 ⟨le_rfl, hT.le⟩).trans hw0⟩
  refine ⟨?_, (hlocal 1 (by norm_num)).2⟩
  intro t ht
  change 0 ≤ t at ht
  have hcont := (hlocal (t + 1) (by linarith : 0 < t + 1)).1 t
    ⟨ht, by linarith⟩
  apply hcont.mono_of_mem_nhdsWithin
  apply mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1))))
  intro s hs
  exact ⟨hs.1, hs.2.le⟩

/-- The single global rough Galerkin limit has its prescribed strong Hhalf trace. -/
theorem CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T))
    (hrep : ∀ T : ℝ, 0 < T → ∃ U : ℝ → CriticalSobolev 3,
      ∃ V : ℝ → CriticalSobolev (-1),
        MemLp U 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff 3 (U t) = criticalCoeff 1 (u t)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff (-1) (V t) =
            fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t)))) :
    ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a :=
  CRITICAL_GLOBAL_STRONG_TRACE_OF_MODAL_EVOLUTION ν a u
    (criticalGalerkinGlobalLimit_criticalCoeff_integral_initial ν a hreal hzero φ hφ g u hu hconv)
    hrep

end

end SingularClosure
