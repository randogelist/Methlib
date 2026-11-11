import SingularClosure.StrongCoefficientContracts
import SingularClosure.SobolevLimitInitial
import SingularClosure.GalerkinCoefficientCompactness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual untruncated Fourier equation of a uniform Galerkin limit

The continuous bilinear tensor convolution determines each full RHS mode.
Compact-time uniform H0 convergence passes through that concrete polynomial
map and through the actual time integral. The resulting coefficient equation
and time derivatives are derived from the Galerkin equations.
Physical distributional product identification is a separate theorem.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Interval Topology

namespace SingularClosure

noncomputable section

theorem fullFourierRhs_continuous (ν : ℝ) (k : Frequency) (i : Fin 3) :
    Continuous (fun c : TorusSobolev 0 => fullFourierRhs ν c k i) := by
  have ht : Continuous (fun c : TorusSobolev 0 =>
      fun j : Fin 3 => divergenceTransportCoefficient k j c c) := by
    apply continuous_pi
    intro j
    exact (divergenceTransportCoefficient k j).continuous.clm_apply
      (continuous_id : Continuous (fun c : TorusSobolev 0 => c))
  exact (continuous_const.mul (torusSobolevH0Coeff_continuous k i)).sub
    ((continuous_apply i).comp ((contDiff_coefficientLeray k).continuous.comp ht))

theorem fullFourierRhs_zero_frequency (ν : ℝ) (c : TorusSobolev 0) (i : Fin 3) :
    fullFourierRhs ν c 0 i = 0 := by
  simp [fullFourierRhs, galerkinFreqSq, coefficientLeray,
    divergenceTransportCoefficient, derivativeSymbol]

/-- The full coefficient polynomial agrees with the literal Galerkin RHS. -/
theorem GalerkinSolution.fullFourierRhs_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    fullFourierRhs ν (g.sobolevState 0 t) k i = galerkinRhs ν N (g.coeff t) k i := by
  have hc := g.sobolevState_coeff 0 ht
  have hs : ∀ p : Frequency, p ∉ cutoffModes N → ∀ j : Fin 3,
      (g.sobolevState 0 t).val p j = 0 := by
    rw [hc]
    exact g.mode_support t ht
  have hsol : SpectralSolenoidal (g.sobolevState 0 t).val := by
    rw [hc]
    exact g.solenoidal t ht
  have htr : (fun j => divergenceTransportCoefficient k j
      (g.sobolevState 0 t) (g.sobolevState 0 t)) = coefficientTransport N (g.coeff t) k := by
    funext j
    have h := (coefficientTransport_eq_divergenceTransport N
      (g.sobolevState 0 t) hs hsol k j).symm
    simpa only [hc] using h
  simp only [fullFourierRhs, hc, htr, galerkinRhs]

theorem GalerkinSolution.coefficient_integral_fullFourierRhs
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {k : Frequency} (hk : k ∈ cutoffModes N) (i : Fin 3)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, fullFourierRhs ν (g.sobolevState 0 r) k i) =
      (g.sobolevState 0 t).val k i - (g.sobolevState 0 s).val k i := by
  rw [g.sobolevState_coeff 0 (hs.trans hst), g.sobolevState_coeff 0 hs]
  calc
    _ = ∫ r in s..t, galerkinRhs ν N (g.coeff r) k i := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hm : r ∈ Icc s t := by simpa only [uIcc_of_le hst] using hr
      exact g.fullFourierRhs_eq r (hs.trans hm.1) k i
    _ = _ := g.coefficient_integral_rhs hk i hs hst

/-- On compact time intervals, the actual RHS coefficients converge uniformly. -/
theorem fullFourierRhs_tendstoUniformlyOn
    (ν : ℝ) (k : Frequency) (i : Fin 3) (T : ℝ)
    {F : ℕ → ℝ → TorusSobolev 0} {u : ℝ → TorusSobolev 0}
    (hF : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn F u atTop (Icc (0 : ℝ) T)) :
    TendstoUniformlyOn (fun n t => fullFourierRhs ν (F n t) k i)
      (fun t => fullFourierRhs ν (u t) k i) atTop (Icc (0 : ℝ) T) := by
  letI : CompactSpace (Icc (0 : ℝ) T) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : ℕ → C(Icc (0 : ℝ) T, TorusSobolev 0) := fun n =>
    ⟨fun t => F n t.val, continuousOn_iff_continuous_restrict.mp (hF n)⟩
  let v : C(Icc (0 : ℝ) T, TorusSobolev 0) :=
    ⟨fun t => u t.val, continuousOn_iff_continuous_restrict.mp hu⟩
  let R : C(TorusSobolev 0, ℂ) := ⟨fun c => fullFourierRhs ν c k i,
    fullFourierRhs_continuous ν k i⟩
  have hf : Tendsto f atTop (𝓝 v) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hconv
  have hr := ((ContinuousMap.continuous_postcomp R).tendsto v).comp hf
  have hr' := ContinuousMap.tendsto_iff_tendstoUniformly.mp hr
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hr'

/-- Every actual compact-time H0 limit satisfies the untruncated modal integral equation. -/
theorem galerkinLimit_coefficient_integral
    (ν : ℝ) (a : Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν a (φ n + 1))
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
theorem galerkinGlobalLimit_coefficient_integral
    (ν : ℝ) (a : Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν a (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    (u t).val k i = (u 0).val k i +
      ∫ r in (0 : ℝ)..t, fullFourierRhs ν (u r) k i := by
  exact galerkinLimit_coefficient_integral ν a φ hφ g (t + 1) (by linarith) u
    (hu.mono (fun r hr => hr.1)) (hconv (t + 1) (by linarith))
    t ⟨ht, by linarith⟩ k i

/-- The genuine integral equation gives the right derivative at zero as well. -/
theorem fullFourierIntegral_hasDerivWithinAt
    (ν : ℝ) (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i +
        ∫ r in (0 : ℝ)..t, fullFourierRhs ν (u r) k i)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun s => (u s).val k i)
      (fullFourierRhs ν (u t) k i) (Ici 0) t := by
  let f : ℝ → ℂ := fun r => fullFourierRhs ν (u (max r 0)) k i
  have hf : Continuous f := (fullFourierRhs_continuous ν k i).comp
    (hu.comp_continuous (continuous_id.max continuous_const) (fun r => le_max_right r 0))
  have hprim := (intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt).const_add ((u 0).val k i)
  have hext (s : ℝ) (hs : 0 ≤ s) :
      (u s).val k i = (u 0).val k i + ∫ r in (0 : ℝ)..s, f r := by
    rw [heq s hs k i]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hm : r ∈ Icc (0 : ℝ) s := by simpa only [uIcc_of_le hs] using hr
    simp only [f, max_eq_left hm.1]
  have hd : HasDerivWithinAt (fun s => (u s).val k i) (f t) (Ici 0) t :=
    hprim.hasDerivWithinAt.congr_of_mem (fun s hs => hext s hs) ht
  simpa only [f, max_eq_left ht] using hd

end

end SingularClosure
