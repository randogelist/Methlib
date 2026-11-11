import SingularClosure.CriticalTraceAnnulus
import SingularClosure.CriticalTraceLimit

/-!
# Strong H^(1/2) trace from L2 H^(3/2) and L2 H^(-1/2) data

The time path is constructed as a uniform limit of its actual Fourier cutoffs.
The hypotheses are coefficient absolute continuity, its a.e. derivative, and
the two Bochner L2 memberships. Strong continuity is a conclusion.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Interval

namespace SingularClosure

noncomputable section

theorem criticalTrace_band_integral_tail_ae
    (q : ℤ) (s : Finset FourierIndex) (N : ℕ)
    (hs : ∀ ki ∈ s, ki ∉ sobolevCutoffIndices N)
    (c : ℝ → FourierCoeff) (u : ℝ → CriticalSobolev q)
    {T : ℝ} (hT : 0 ≤ T)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hc : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), c t = criticalCoeff q (u t)) :
    (∫ t in (0 : ℝ)..T, ‖criticalFiniteBandState q s (c t)‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ‖u t - criticalSobolevCutoff q N (u t)‖ ^ 2 := by
  have hm : MemLp (fun t => criticalFiniteBandState q s (c t)) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (criticalFiniteBandState_memLp q s u hu).ae_eq
      (hc.mono fun t ht => congrArg (criticalFiniteBandState q s) ht.symm)
  apply intervalIntegral.integral_mono_ae_restrict hT
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
      (criticalTrace_integrable_norm_sq hm)
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
      (criticalTrace_integrable_norm_sq (hu.sub ((criticalSobolevCutoff q N).comp_memLp' hu)))
  · filter_upwards [hc] with t ht
    rw [ht]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (criticalFiniteBandState_tail_norm_le q s N hs (u t)) 2

/-- Stage 7 with each finite-band quantity dominated by actual full-space tails. -/
theorem criticalTrace_band_pointwise_tail_bound
    (s : Finset FourierIndex) (N : ℕ)
    (hs : ∀ ki ∈ s, ki ∉ sobolevCutoffIndices N)
    (c r : ℝ → FourierCoeff)
    (u : ℝ → CriticalSobolev 3) (v : ℝ → CriticalSobolev (-1))
    {T : ℝ} (hT : 0 < T)
    (hre : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).re) 0 T)
    (him : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).im) 0 T)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ki : ↥s,
      HasDerivAt (fun τ => c τ ki.val.1 ki.val.2) (r t ki.val.1 ki.val.2) t)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hc : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), c t = criticalCoeff 3 (u t))
    (hr : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), r t = criticalCoeff (-1) (v t)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖criticalFiniteBandState 1 s (c t)‖ ^ 2 ≤
        (∫ τ in (0 : ℝ)..T, ‖u τ - criticalSobolevCutoff 3 N (u τ)‖ ^ 2) / T +
          2 * Real.sqrt (∫ τ in (0 : ℝ)..T,
            ‖v τ - criticalSobolevCutoff (-1) N (v τ)‖ ^ 2) *
            Real.sqrt (∫ τ in (0 : ℝ)..T,
              ‖u τ - criticalSobolevCutoff 3 N (u τ)‖ ^ 2) := by
  have hhi : MemLp (fun t => criticalFiniteBandState 3 s (c t)) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (criticalFiniteBandState_memLp 3 s u hu).ae_eq
      (hc.mono fun t ht => congrArg (criticalFiniteBandState 3 s) ht.symm)
  have hlo : MemLp (fun t => criticalFiniteBandState (-1) s (r t)) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (criticalFiniteBandState_memLp (-1) s v hv).ae_eq
      (hr.mono fun t ht => congrArg (criticalFiniteBandState (-1) s) ht.symm)
  have hA := criticalFiniteBandEnergy_absolutelyContinuous s c hre him
  have hAc : ContinuousOn (fun t => ‖criticalFiniteBandState 1 s (c t)‖ ^ 2)
      (Icc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT.le] using hA.continuousOn
  have hAvg : (∫ τ in (0 : ℝ)..T, ‖criticalFiniteBandState 1 s (c τ)‖ ^ 2) ≤
      ∫ τ in (0 : ℝ)..T, ‖u τ - criticalSobolevCutoff 3 N (u τ)‖ ^ 2 := by
    apply intervalIntegral.integral_mono_ae_restrict hT.le
      (hAc.intervalIntegrable_of_Icc hT.le)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr
        (criticalTrace_integrable_norm_sq (hu.sub ((criticalSobolevCutoff 3 N).comp_memLp' hu)))
    · filter_upwards [hc] with t ht
      rw [ht]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((criticalFiniteBandState_norm_mono (by norm_num : (1 : ℤ) ≤ 3) s _).trans
          (criticalFiniteBandState_tail_norm_le 3 s N hs (u t))) 2
  have hLo := criticalTrace_band_integral_tail_ae (-1) s N hs r v hT.le hv hr
  have hHi := criticalTrace_band_integral_tail_ae 3 s N hs c u hT.le hu hc
  intro t ht
  refine (CRITICAL_FINITE_FOURIER_BAND_TRACE_BOUND s c r hT hre him hderiv
    hlo.norm hhi.norm t ht).trans ?_
  apply add_le_add (div_le_div_of_nonneg_right hAvg hT.le)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hLo) (by norm_num))
    (Real.sqrt_le_sqrt hHi) (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The coefficient paths produce an actual strongly continuous critical trace. -/
theorem CRITICAL_HHALF_STRONG_TRACE
    (c r : ℝ → FourierCoeff)
    (u : ℝ → CriticalSobolev 3) (v : ℝ → CriticalSobolev (-1))
    {T : ℝ} (hT : 0 < T)
    (hre : ∀ k i,
      AbsolutelyContinuousOnInterval (fun t => (c t k i).re) 0 T)
    (him : ∀ k i,
      AbsolutelyContinuousOnInterval (fun t => (c t k i).im) 0 T)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ k i,
      HasDerivAt (fun τ => c τ k i) (r t k i) t)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hc : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), c t = criticalCoeff 3 (u t))
    (hr : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), r t = criticalCoeff (-1) (v t))
    (a : CriticalSobolev 1) (hinit : c 0 = criticalCoeff 1 a) :
    ∃ w : ℝ → CriticalSobolev 1,
      ContinuousOn w (Icc (0 : ℝ) T) ∧ w 0 = a ∧
      (∀ t ∈ Icc (0 : ℝ) T, criticalCoeff 1 (w t) = c t) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        w t = criticalSobolevLower 1 3 (by norm_num) (u t)) := by
  classical
  let F : ℕ → ℝ → CriticalSobolev 1 := fun N t =>
    criticalBandSobolev 1 (sobolevCutoffIndices N) (c t)
  let U : ℕ → ℝ := fun N => ∫ t in (0 : ℝ)..T,
    ‖u t - criticalSobolevCutoff 3 N (u t)‖ ^ 2
  let V : ℕ → ℝ := fun N => ∫ t in (0 : ℝ)..T,
    ‖v t - criticalSobolevCutoff (-1) N (v t)‖ ^ 2
  let d : ℕ → ℝ := fun N => U N / T + 2 * Real.sqrt (V N) * Real.sqrt (U N)
  have hU : Tendsto U atTop (𝓝 (0 : ℝ)) :=
    CRITICAL_SOBOLEV_CUTOFF_INTERVAL_L2_TAIL 3 u hT.le hu
  have hV : Tendsto V atTop (𝓝 (0 : ℝ)) :=
    CRITICAL_SOBOLEV_CUTOFF_INTERVAL_L2_TAIL (-1) v hT.le hv
  have hd : Tendsto d atTop (𝓝 (0 : ℝ)) := by
    have h := (hU.div_const T).add
      (((Real.continuous_sqrt.tendsto 0).comp hV).const_mul 2 |>.mul
        ((Real.continuous_sqrt.tendsto 0).comp hU))
    simpa only [d, Function.comp_def, Real.sqrt_zero, zero_div, mul_zero, add_zero] using h
  have hcont : ∀ k i, ContinuousOn (fun t => c t k i) (Icc (0 : ℝ) T) := by
    intro k i
    have hR : ContinuousOn (fun t => (c t k i).re) (Icc (0 : ℝ) T) := by
      simpa only [uIcc_of_le hT.le] using (hre k i).continuousOn
    have hI : ContinuousOn (fun t => (c t k i).im) (Icc (0 : ℝ) T) := by
      simpa only [uIcc_of_le hT.le] using (him k i).continuousOn
    have hcomplex : ContinuousOn
        (fun t => ((c t k i).re : ℂ) + ((c t k i).im : ℂ) * Complex.I)
        (Icc (0 : ℝ) T) :=
      (Complex.continuous_ofReal.comp_continuousOn hR).add
        ((Complex.continuous_ofReal.comp_continuousOn hI).mul continuousOn_const)
    simpa only [Complex.re_add_im] using hcomplex
  have hF : ∀ N, ContinuousOn (F N) (Icc (0 : ℝ) T) := by
    intro N
    exact criticalBandSobolev_continuousOn 1 (sobolevCutoffIndices N) c _
      (fun ki _ => hcont ki.1 ki.2)
  have hann : ∀ N K L : ℕ, N ≤ K → K ≤ L → ∀ t ∈ Icc (0 : ℝ) T,
      ‖F L t - F K t‖ ^ 2 ≤ d N := by
    intro N K L hNK hKL t ht
    have hs : ∀ ki ∈ criticalFourierAnnulus K L, ki ∉ sobolevCutoffIndices N := by
      intro ki hki hkiN
      exact (Finset.mem_sdiff.mp hki).2 (criticalTrace_cutoffIndices_mono hNK hkiN)
    change ‖criticalBandSobolev 1 (sobolevCutoffIndices L) (c t) -
      criticalBandSobolev 1 (sobolevCutoffIndices K) (c t)‖ ^ 2 ≤ _
    rw [criticalBandSobolev_sub_eq_annulus 1 hKL, criticalBandSobolev_norm_sq]
    exact criticalTrace_band_pointwise_tail_bound (criticalFourierAnnulus K L) N hs
      c r u v hT (fun ki => hre ki.val.1 ki.val.2) (fun ki => him ki.val.1 ki.val.2)
      (hderiv.mono fun τ hτ ki => hτ ki.val.1 ki.val.2) hu hv hc hr t ht
  have hband : ∀ N m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n → ∀ t ∈ Icc (0 : ℝ) T,
      ‖F m t - F n t‖ ^ 2 ≤ d N := by
    intro N m hm n hn t ht
    rcases le_total n m with hnm | hmn
    · exact hann N n m hn hnm t ht
    · rw [norm_sub_rev]
      exact hann N m n hm hmn t ht
  have hFinit : Tendsto (fun N => F N 0) atTop (𝓝 a) := by
    simpa only [F, hinit] using criticalBandSobolev_initial_tendsto 1 a
  obtain ⟨w, hwc, hwu, hw0⟩ :=
    CRITICAL_HHALF_TRACE_EXISTS_OF_BAND_ENERGY F d hT.le hF hd hband a hFinit
  have hwcoeff : ∀ t ∈ Icc (0 : ℝ) T, criticalCoeff 1 (w t) = c t := by
    intro t ht
    funext k i
    have hlim := (criticalCoeff_continuous 1 k i).continuousAt.tendsto.comp
      (hwu.tendsto_at ht)
    simp only [Function.comp_def] at hlim
    have hevent : ∀ᶠ N in atTop, criticalCoeff 1 (F N t) k i = c t k i := by
      filter_upwards [eventually_mem_sobolevCutoffModes k] with N hN
      simp only [F, criticalBandSobolev_coeff, criticalTrace_mem_cutoffIndices, if_pos hN]
    exact tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (hevent.mono fun N hN => hN.symm))
  refine ⟨w, hwc, hw0, hwcoeff, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with t ht htI
  apply criticalCoeff_injective 1
  rw [hwcoeff t htI, ht, criticalSobolevLower_coeff]

end

end SingularClosure
