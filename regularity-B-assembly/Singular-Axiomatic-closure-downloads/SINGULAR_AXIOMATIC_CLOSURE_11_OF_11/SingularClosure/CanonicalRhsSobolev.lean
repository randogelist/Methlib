import SingularClosure.FourierLimitEquation
import SingularClosure.HighOrderTimeModulus
import SingularClosure.SobolevCoefficientCalculus

/-!
# The actual Hilbert-valued RHS of a canonical Galerkin limit

The concrete full Fourier RHS belongs to every Sobolev order by the proved
uniform Galerkin RHS bounds and weighted-lp lower semicontinuity. Its strong
continuity follows from coefficient continuity and one higher uniform bound.
The actual modal integral equation then identifies the Bochner time derivative.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.rhsSobolev_coeff
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    (g.rhsSobolev s t).val k i =
      if k ∈ cutoffModes N then fullFourierRhs ν (g.sobolevState 0 t) k i else 0 := by
  rw [g.rhsSobolev_eq_finiteSobolev s t ht, finiteSobolev_coeff,
    g.fullFourierRhs_eq t ht k i]
  rfl

theorem canonical_rhsSobolev_coeff_tendsto
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ℝ → TorusSobolev 0) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    Tendsto (fun n =>
      ((canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t).val k i)
      atTop (𝓝 (fullFourierRhs ν (u t) k i)) := by
  have hpoint := (hconv (t + 1) (by linarith)).tendsto_at
    (show t ∈ Icc (0 : ℝ) (t + 1) from ⟨ht, by linarith⟩)
  have hfull := ((fullFourierRhs_continuous ν k i).tendsto (u t)).comp hpoint
  by_cases hk : k = 0
  · subst k
    simp only [fullFourierRhs_zero_frequency]
    have heq : (fun n =>
        ((canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t).val 0 i) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      rw [(canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev_coeff s t ht 0 i,
        if_neg (cutoffModes_zero_not_mem _)]
    rw [heq]
    exact tendsto_const_nhds
  · apply hfull.congr'
    filter_upwards [eventually_mem_cutoffModes_strictMono φ hφ k hk] with n hn
    exact (((canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev_coeff s t ht k i).trans
      (if_pos hn)).symm

theorem canonical_fullFourierRhs_mem
    (hAX6 : AX6Statement) (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ℝ → TorusSobolev 0) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Memℓp (sobolevWeightedCoeff s (fullFourierRhs ν (u t))) 2 := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_HIGH_ORDER_RHS hAX6 ν hν a ha
    (t + 1) (by linarith) s
  have hbound (n : ℕ) :
      ‖(canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t‖ ≤ B + 1 := by
    have h := hb (φ n + 1) (by omega)
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)) t ⟨ht, by linarith⟩
    nlinarith [sq_nonneg
      (‖(canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t‖ - 1)]
  exact (torusSobolev_limit_mem_and_norm_le s
    (fun n => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t)
    (fullFourierRhs ν (u t)) (B + 1) hbound
    (canonical_rhsSobolev_coeff_tendsto ν hν a ha u φ hφ hconv s t ht)).choose

def canonicalLimitRhsSobolev
    (hAX6 : AX6Statement) (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ℝ → TorusSobolev 0) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (s : ℕ) (t : ℝ) : TorusSobolev s :=
  if ht : 0 ≤ t then
    ⟨fullFourierRhs ν (u t), canonical_fullFourierRhs_mem hAX6 ν hν a ha u φ hφ hconv s t ht⟩
  else 0

section CanonicalLimit

variable (hAX6 : AX6Statement) (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
variable (u : ℝ → TorusSobolev 0) (φ : ℕ → ℕ) (hφ : StrictMono φ)
variable (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
  (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
  u atTop (Icc (0 : ℝ) T))

local notation "R" => canonicalLimitRhsSobolev hAX6 ν hν a ha u φ hφ hconv

theorem canonicalLimitRhsSobolev_coeff (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (R s t).val = fullFourierRhs ν (u t) := by
  have heq : R s t = (⟨fullFourierRhs ν (u t),
      canonical_fullFourierRhs_mem hAX6 ν hν a ha u φ hφ hconv s t ht⟩ :
        TorusSobolev s) := by
    unfold canonicalLimitRhsSobolev
    exact dif_pos ht
  exact congrArg (fun c : TorusSobolev s => c.val) heq

theorem canonicalLimitRhsSobolev_inclusion (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    torusSobolevInclusion s (R (s + 1) t) = R s t := by
  apply Subtype.ext
  rw [torusSobolevInclusion_coeff,
    canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv (s + 1) t ht,
    canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv s t ht]

theorem canonicalLimitRhsSobolev_uniform_bound (s : ℕ) (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖R s t‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_HIGH_ORDER_RHS hAX6 ν hν a ha T hT s
  refine ⟨B + 1, by linarith, ?_⟩
  intro t ht
  have hbound (n : ℕ) :
      ‖(canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t‖ ≤ B + 1 := by
    have h := hb (φ n + 1) (by omega)
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)) t ht
    nlinarith [sq_nonneg
      (‖(canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t‖ - 1)]
  obtain ⟨hc, hn⟩ := torusSobolev_limit_mem_and_norm_le s
    (fun n => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).rhsSobolev s t)
    (fullFourierRhs ν (u t)) (B + 1) hbound
    (canonical_rhsSobolev_coeff_tendsto ν hν a ha u φ hφ hconv s t ht.1)
  have heq : R s t = (⟨fullFourierRhs ν (u t), hc⟩ : TorusSobolev s) := by
    apply Subtype.ext
    exact canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv s t ht.1
  calc
    ‖R s t‖ = @norm (TorusSobolev s) inferInstance
        ⟨fullFourierRhs ν (u t), hc⟩ :=
      congrArg (@norm (TorusSobolev s) inferInstance) heq
    _ ≤ B + 1 := hn

theorem canonicalLimitRhsSobolev_continuousOn_Icc
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (T : ℝ) (hT : 0 < T) :
    ContinuousOn (R s) (Icc (0 : ℝ) T) := by
  obtain ⟨B, _, hb⟩ := canonicalLimitRhsSobolev_uniform_bound
    hAX6 ν hν a ha u φ hφ hconv (s + 1) T hT
  have hcoeff (k : Frequency) (i : Fin 3) :
      ContinuousOn (fun t => (R (s + 1) t).val k i) (Icc (0 : ℝ) T) := by
    apply ((fullFourierRhs_continuous ν k i).comp_continuousOn
      (hu.mono (fun t ht => ht.1))).congr
    intro t ht
    exact congrArg (fun c : FourierCoeff => c k i)
      (canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv (s + 1) t ht.1)
  have hc := torusSobolevInclusion_continuousOn_of_coeff_continuousOn
    s (R (s + 1)) (Icc (0 : ℝ) T) B hb hcoeff
  apply hc.congr
  intro t ht
  exact (canonicalLimitRhsSobolev_inclusion hAX6 ν hν a ha u φ hφ hconv s t ht.1).symm

theorem canonicalLimitRhsSobolev_continuousOn
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) : ContinuousOn (R s) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hc := canonicalLimitRhsSobolev_continuousOn_Icc
    hAX6 ν hν a ha u φ hφ hconv hu s (t + 1) (by linarith) t ⟨ht, by linarith⟩
  apply hc.mono_of_mem_nhdsWithin
  apply mem_of_superset (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1))))
  intro z hz
  exact ⟨hz.1, hz.2.le⟩

theorem canonicalLimitRhsSobolev_intervalIntegrable
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (R s) volume 0 T :=
  ((canonicalLimitRhsSobolev_continuousOn hAX6 ν hν a ha u φ hφ hconv hu s).mono
    (fun t ht => ht.1)).intervalIntegrable_of_Icc hT

theorem canonicalLimitRhsSobolev_memLp
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (T : ℝ) (p : ℝ≥0∞) :
    MemLp (R s) p (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) := ⟨by simp⟩
  have hc := (canonicalLimitRhsSobolev_continuousOn
    hAX6 ν hν a ha u φ hφ hconv hu s).mono (fun t (ht : t ∈ Icc (0 : ℝ) T) => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply MemLp.of_bound
    (hc.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

theorem canonicalLimitRhsSobolev_coefficient_integral
    (hu : ContinuousOn u (Ici 0)) (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    (u t).val k i = (u 0).val k i + ∫ z in (0 : ℝ)..t, (R 0 z).val k i := by
  rw [galerkinGlobalLimit_coefficient_integral ν a φ hφ
    (fun n => canonicalGalerkinSolution ν hν a ha (φ n + 1)) u hu hconv t ht k i]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  have hm : z ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht] using hz
  exact (congrArg (fun c : FourierCoeff => c k i)
    (canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv 0 z hm.1)).symm

theorem canonicalLimitRhsSobolev_time_integral
    (hu : ContinuousOn u (Ici 0)) (t : ℝ) (ht : 0 ≤ t) :
    u t = u 0 + ∫ z in (0 : ℝ)..t, R 0 z :=
  torusSobolev_integral_eq_of_coefficient_integral 0 u (R 0) t
    (canonicalLimitRhsSobolev_intervalIntegrable hAX6 ν hν a ha u φ hφ hconv hu 0 t ht)
    (canonicalLimitRhsSobolev_coefficient_integral hAX6 ν hν a ha u φ hφ hconv hu t ht)

theorem canonicalLimitRhsSobolev_hasDerivWithinAt
    (hu : ContinuousOn u (Ici 0)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt u (R 0 t) (Ici 0) t :=
  torusSobolev_hasDerivWithinAt_of_coefficient_integral 0 u (R 0)
    (canonicalLimitRhsSobolev_continuousOn hAX6 ν hν a ha u φ hφ hconv hu 0)
    (canonicalLimitRhsSobolev_coefficient_integral hAX6 ν hν a ha u φ hφ hconv hu) t ht

/-- Any higher-order representative of the same coefficient curve satisfies
the actual Bochner equation in that higher Sobolev space. -/
theorem canonicalLimitRhsSobolev_coefficient_integral_order
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (v : ℝ → TorusSobolev s)
    (hv : ∀ t : ℝ, 0 ≤ t → (v t).val = (u t).val)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    (v t).val k i = (v 0).val k i + ∫ z in (0 : ℝ)..t, (R s z).val k i := by
  rw [hv t ht, hv 0 le_rfl,
    canonicalLimitRhsSobolev_coefficient_integral hAX6 ν hν a ha u φ hφ hconv hu t ht k i]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  have hm : z ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht] using hz
  exact congrArg (fun c : FourierCoeff => c k i)
    ((canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv 0 z hm.1).trans
      (canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv s z hm.1).symm)

theorem canonicalLimitRhsSobolev_time_integral_order
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (v : ℝ → TorusSobolev s)
    (hv : ∀ t : ℝ, 0 ≤ t → (v t).val = (u t).val)
    (t : ℝ) (ht : 0 ≤ t) :
    v t = v 0 + ∫ z in (0 : ℝ)..t, R s z :=
  torusSobolev_integral_eq_of_coefficient_integral s v (R s) t
    (canonicalLimitRhsSobolev_intervalIntegrable hAX6 ν hν a ha u φ hφ hconv hu s t ht)
    (canonicalLimitRhsSobolev_coefficient_integral_order
      hAX6 ν hν a ha u φ hφ hconv hu s v hv t ht)

theorem canonicalLimitRhsSobolev_hasDerivWithinAt_order
    (hu : ContinuousOn u (Ici 0)) (s : ℕ) (v : ℝ → TorusSobolev s)
    (hv : ∀ t : ℝ, 0 ≤ t → (v t).val = (u t).val)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt v (R s t) (Ici 0) t :=
  torusSobolev_hasDerivWithinAt_of_coefficient_integral s v (R s)
    (canonicalLimitRhsSobolev_continuousOn hAX6 ν hν a ha u φ hφ hconv hu s)
    (canonicalLimitRhsSobolev_coefficient_integral_order
      hAX6 ν hν a ha u φ hφ hconv hu s v hv) t ht

end CanonicalLimit

end

end SingularClosure
