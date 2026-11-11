import Mathlib

/-!
# Absolute-continuity trace estimates for critical Fourier bands

The scalar estimate bounds the maximum energy of a finite Fourier band by
its time average and the product of its two dual time-L2 norms. Continuity
of the energy is obtained from absolute continuity. No continuity predicate
for an infinite-dimensional NSE solution is assumed.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Interval Topology ENNReal

namespace SingularClosure

noncomputable section

/-- A uniform oscillation bound converts a time average into a pointwise bound. -/
theorem criticalTrace_le_average_add_variation
    (A : ℝ → ℝ) {T D : ℝ} (hT : 0 < T)
    (hA : ContinuousOn A (Icc (0 : ℝ) T))
    (hvariation : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      A t - A s ≤ D) :
    ∀ t ∈ Icc (0 : ℝ) T,
      A t ≤ (∫ s in (0 : ℝ)..T, A s) / T + D := by
  intro t ht
  have hcompare : (∫ s in (0 : ℝ)..T, A t) ≤
      ∫ s in (0 : ℝ)..T, A s + D := by
    apply intervalIntegral.integral_mono_on hT.le intervalIntegrable_const
      ((hA.add continuousOn_const).intervalIntegrable_of_Icc hT.le)
    intro s hs
    change A t ≤ A s + D
    linarith [hvariation s hs t ht]
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.intervalIntegrable_of_Icc hT.le)
      intervalIntegrable_const, intervalIntegral.integral_const] at hcompare
  simp only [sub_zero, smul_eq_mul] at hcompare
  have havg : A t - D ≤ (∫ s in (0 : ℝ)..T, A s) / T := by
    apply (le_div_iff₀ hT).mpr
    nlinarith
  linarith

/-- Absolute continuity controls every two-time energy difference by total variation. -/
theorem criticalTrace_abs_sub_le_integral_abs_deriv
    (A : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hA : AbsolutelyContinuousOnInterval A 0 T)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    |A t - A s| ≤ ∫ r in (0 : ℝ)..T, |deriv A r| := by
  have hclosed : uIcc s t ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    intro r hr
    rcases le_total s t with hst | hts
    · rw [uIcc_of_le hst] at hr
      exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    · rw [uIcc_of_ge hts] at hr
      exact ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
  have hopen : uIoc s t ⊆ uIoc (0 : ℝ) T := by
    rw [uIoc_of_le hT]
    intro r hr
    rcases le_total s t with hst | hts
    · rw [uIoc_of_le hst] at hr
      exact ⟨lt_of_le_of_lt hs.1 hr.1, hr.2.trans ht.2⟩
    · rw [uIoc_of_ge hts] at hr
      exact ⟨lt_of_le_of_lt ht.1 hr.1, hr.2.trans hs.2⟩
  calc
    _ = abs (∫ r in s..t, deriv A r) :=
      congrArg abs (hA.mono hclosed).integral_deriv_eq_sub.symm
    _ ≤ abs (∫ r in s..t, |deriv A r|) := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_abs_integral_norm
          (f := fun r => deriv A r) (a := s) (b := t) (μ := volume))
    _ ≤ abs (∫ r in (0 : ℝ)..T, |deriv A r|) :=
      intervalIntegral.abs_integral_mono_interval hopen
        (Filter.Eventually.of_forall (fun r => abs_nonneg _))
        hA.intervalIntegrable_deriv.abs
    _ = _ := abs_of_nonneg
      (intervalIntegral.integral_nonneg_of_forall hT (fun r => abs_nonneg _))

/-- L2 Cauchy--Schwarz on the exact finite forward time interval. -/
theorem criticalTrace_integral_mul_le_sqrt
    {f g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hf0 : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] f)
    (hg0 : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] g) :
    (∫ t in (0 : ℝ)..T, f t * g t) ≤
      Real.sqrt (∫ t in (0 : ℝ)..T, (f t) ^ 2) *
      Real.sqrt (∫ t in (0 : ℝ)..T, (g t) ^ 2) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Icc (0 : ℝ) T)) Real.HolderConjugate.two_two
    hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow,
    intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc] using h

/-- The band-energy trace estimate with merely L2 dual factors.

For a Fourier band, `A` is its squared H^(1/2) norm, `f` the band H^(-1/2)
norm of the time derivative, and `g` the band H^(3/2) norm. -/
theorem CRITICAL_BAND_ENERGY_TRACE_BOUND
    (A f g : ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hA : AbsolutelyContinuousOnInterval A 0 T)
    (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hf0 : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] f)
    (hg0 : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) T)] g)
    (hd : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      |deriv A t| ≤ 2 * (f t * g t)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      A t ≤ (∫ s in (0 : ℝ)..T, A s) / T +
        2 * Real.sqrt (∫ s in (0 : ℝ)..T, (f s) ^ 2) *
          Real.sqrt (∫ s in (0 : ℝ)..T, (g s) ^ 2) := by
  have hAc : ContinuousOn A (Icc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT.le] using hA.continuousOn
  have hprod : IntervalIntegrable (fun t => 2 * (f t * g t)) volume 0 T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr
    exact (hf.integrable_mul hg).const_mul 2
  have hderiv : (∫ t in (0 : ℝ)..T, |deriv A t|) ≤
      2 * (∫ t in (0 : ℝ)..T, f t * g t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_ae_restrict hT.le
      hA.intervalIntegrable_deriv.abs hprod hd
  have hCS := criticalTrace_integral_mul_le_sqrt hT.le hf hg hf0 hg0
  have hvar : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      A t - A s ≤ ∫ r in (0 : ℝ)..T, |deriv A r| := by
    intro s hs t ht
    exact (le_abs_self _).trans
      (criticalTrace_abs_sub_le_integral_abs_deriv A hT.le hA hs ht)
  intro t ht
  have havg := criticalTrace_le_average_add_variation A hT hAc hvar t ht
  nlinarith

end

end SingularClosure
