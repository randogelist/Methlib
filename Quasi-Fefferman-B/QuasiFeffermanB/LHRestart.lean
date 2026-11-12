import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalWeakGradient
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.InnerProductSpace.Basic
import QuasiFeffermanB.TimeTranslate

/-! Restart prerequisites on the native physical Leray--Hopf carrier.
No solution, comparison or restart conclusion is included in a premise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def LHGoodEnergyTime (ν : ℝ) (v : Velocity)
    (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (s : ℝ) : Prop :=
  0 < s ∧ CriticalPhysicalH1 (v s) (G s) ∧
    ∀ t : ℝ, s ≤ t →
      physicalEnergy (v t) +
        2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)

theorem lh_ae_good_energy_time
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), LHGoodEnergyTime ν v G s := by
  have hall : ∀ᵐ s ∂volume, ∀ n : ℕ,
      s ∈ Ioc (0 : ℝ) ((n : ℝ) + 1) →
        CriticalPhysicalH1 (v s) (G s) ∧
        ∀ t ∈ Icc s ((n : ℝ) + 1),
          physicalEnergy (v t) +
            2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤
              physicalEnergy (v s) := by
    rw [ae_all_iff]
    intro n
    exact (ae_restrict_iff' measurableSet_Ioc).mp
      ((hv.spatial_H1 ((n : ℝ) + 1) (by positivity)).and
        (hv.energy_intervals ((n : ℝ) + 1) (by positivity)))
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [hall] with s hs
  intro hspos
  obtain ⟨n, hn⟩ := exists_nat_gt s
  refine ⟨hspos, (hs n ⟨hspos, by linarith⟩).1, ?_⟩
  intro t hst
  obtain ⟨m, hm⟩ := exists_nat_gt t
  exact (hs m ⟨hspos, by linarith⟩).2 t ⟨hst, by linarith⟩

theorem restart_representative_norm_sq (f : Field)
    (hf : MemLp f 2 (volume.restrict unitCube)) :
    ‖criticalL2Representative f‖ ^ 2 = physicalEnergy f := by
  rw [criticalL2Representative_eq f hf, ← real_inner_self_eq_norm_sq,
    L2.inner_def, physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem restart_representative_inner (f g : Field)
    (hf : MemLp f 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube)) :
    inner ℝ (criticalL2Representative f) (criticalL2Representative g) =
      physicalFieldInner f g := by
  rw [criticalL2Representative_eq f hf, criticalL2Representative_eq g hg]
  exact (critical_physicalFieldInner_eq_L2_inner f g hf hg).symm

theorem strong_tendsto_of_inner_and_norm_bound
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {l : Filter ι} {f : ι → E} {a : E}
    (hinner : Tendsto (fun i => inner ℝ (f i) a) l (𝓝 (‖a‖ ^ 2)))
    (hbound : ∀ᶠ i in l, ‖f i‖ ^ 2 ≤ ‖a‖ ^ 2) :
    Tendsto f l (𝓝 a) := by
  have hupper : Tendsto (fun i => 2 * ‖a‖ ^ 2 - 2 * inner ℝ (f i) a)
      l (𝓝 0) := by
    have hconst : Tendsto (fun _ : ι => 2 * ‖a‖ ^ 2) l (𝓝 (2 * ‖a‖ ^ 2)) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun i => 2 * inner ℝ (f i) a)
        l (𝓝 (2 * ‖a‖ ^ 2)) := tendsto_const_nhds.mul hinner
    simpa only [sub_self] using hconst.sub htwo
  have hsq : Tendsto (fun i => ‖f i - a‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg ‖f i - a‖))
      ?_ hupper
    filter_upwards [hbound] with i hi
    rw [norm_sub_sq_real]
    linarith
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn : Tendsto (fun i => ‖f i - a‖) l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
      using hsqrt
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn

theorem lh_energy_le_from_start
    {ν : ℝ} {v : Velocity} {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hν : 0 ≤ ν) {s t : ℝ}
    (hE : ∀ r : ℝ, s ≤ r → physicalEnergy (v r) +
      2 * ν * (∫ q in s..r, criticalGradientEnergy (G q)) ≤ physicalEnergy (v s))
    (hst : s ≤ t) :
    physicalEnergy (v t) ≤ physicalEnergy (v s) := by
  have hD : 0 ≤ ∫ r in s..t, criticalGradientEnergy (G r) :=
    intervalIntegral.integral_nonneg_of_forall hst
      (fun r => criticalGradientEnergy_nonneg (G r))
  have hprod : 0 ≤ 2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) :=
    mul_nonneg (mul_nonneg (by norm_num) hν) hD
  linarith only [hE t hst, hprod]

theorem lh_energy_le_at_good_time
    {ν : ℝ} {v : Velocity} {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hν : 0 ≤ ν) {s t : ℝ} (hs : LHGoodEnergyTime ν v G s) (hst : s ≤ t) :
    physicalEnergy (v t) ≤ physicalEnergy (v s) :=
  lh_energy_le_from_start hν hs.2.2 hst

theorem lh_strong_right_trace_of_energy_start
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : 0 ≤ s)
    (hE : ∀ r : ℝ, s ≤ r → physicalEnergy (v r) +
      2 * ν * (∫ q in s..r, criticalGradientEnergy (G q)) ≤ physicalEnergy (v s)) :
    Tendsto (fun t => criticalL2Representative (v t))
      (𝓝[>] s) (𝓝 (criticalL2Representative (v s))) := by
  have hvs := hv.velocity_L2 s hs
  have hc := (hv.weak_continuity (v s) hvs) s hs
  have hi : Tendsto (fun t => physicalFieldInner (v t) (v s))
      (𝓝[>] s) (𝓝 (physicalFieldInner (v s) (v s))) :=
    hc.tendsto.mono_left (nhdsWithin_mono _
      (show Ioi s ⊆ Ici (0 : ℝ) from fun t ht => hs.trans ht.le))
  apply strong_tendsto_of_inner_and_norm_bound
  · have hpair : (fun t => inner ℝ (criticalL2Representative (v t))
        (criticalL2Representative (v s))) =ᶠ[𝓝[>] s]
        (fun t => physicalFieldInner (v t) (v s)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact restart_representative_inner (v t) (v s)
        (hv.velocity_L2 t (hs.trans ht.le)) hvs
    have hself : physicalFieldInner (v s) (v s) =
        ‖criticalL2Representative (v s)‖ ^ 2 := by
      rw [← restart_representative_inner (v s) (v s) hvs hvs,
        real_inner_self_eq_norm_sq]
    rw [hself] at hi
    exact hi.congr' hpair.symm
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [restart_representative_norm_sq (v t)
      (hv.velocity_L2 t (hs.trans ht.le)),
      restart_representative_norm_sq (v s) hvs]
    exact lh_energy_le_from_start hν hE ht.le

theorem lh_strong_right_trace_at_good_time
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : LHGoodEnergyTime ν v G s) :
    Tendsto (fun t => criticalL2Representative (v t))
      (𝓝[>] s) (𝓝 (criticalL2Representative (v s))) :=
  lh_strong_right_trace_of_energy_start hv hν hs.1.le hs.2.2

theorem restart_representative_edist (f : Field)
    (hf : MemLp f 2 (volume.restrict unitCube)) (a : CriticalPhysicalL2) :
    edist (criticalL2Representative f) a =
      eLpNorm (f - (a : Field)) 2 (volume.restrict unitCube) := by
  rw [criticalL2Representative_eq f hf, Lp.edist_def]
  apply eLpNorm_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [Pi.sub_apply, hx]

theorem timeTranslate_tendsto_nhdsWithin_right (s : ℝ) :
    Tendsto (fun t : ℝ => t + s) (𝓝[>] (0 : ℝ)) (𝓝[>] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => t + s) := continuous_id.add continuous_const
    simpa only [zero_add] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change (0 : ℝ) < t at ht
    change s < t + s
    linarith

theorem lh_shifted_strong_trace_of_energy_start
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : 0 ≤ s)
    (hE : ∀ r : ℝ, s ≤ r → physicalEnergy (v r) +
      2 * ν * (∫ q in s..r, criticalGradientEnergy (G q)) ≤ physicalEnergy (v s)) :
    Tendsto (fun t => eLpNorm
      (timeTranslate s v t - (criticalL2Representative (v s) : Field))
      2 (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (lh_strong_right_trace_of_energy_start hv hν hs hE).comp
    (timeTranslate_tendsto_nhdsWithin_right s)
  have he : Tendsto (fun t => edist (criticalL2Representative (v (t + s)))
      (criticalL2Representative (v s))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, edist_self] using h.edist tendsto_const_nhds
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (0 : ℝ) < t at ht
  exact restart_representative_edist (v (t + s))
    (hv.velocity_L2 (t + s) (by linarith)) (criticalL2Representative (v s))

theorem lh_shifted_strong_trace_at_good_time
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : LHGoodEnergyTime ν v G s) :
    Tendsto (fun t => eLpNorm
      (timeTranslate s v t - (criticalL2Representative (v s) : Field))
      2 (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  lh_shifted_strong_trace_of_energy_start hv hν hs.1.le hs.2.2

theorem LH_RESTART_FROM_ENERGY_START
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : 0 ≤ s)
    (hE : ∀ r : ℝ, s ≤ r → physicalEnergy (v r) +
      2 * ν * (∫ q in s..r, criticalGradientEnergy (G q)) ≤ physicalEnergy (v s)) :
    CriticalLerayHopf ν (criticalL2Representative (v s))
      (timeTranslate s v) (timeTranslate s G) := by
  have hs0 : 0 ≤ s := hs
  have hvs := hv.velocity_L2 s hs0
  refine {
    momentum := timeTranslate_integrated_momentum hv.momentum hs0
    velocity_L2 := fun t ht => hv.velocity_L2 (t + s) (add_nonneg ht hs0)
    velocity_energy_class := fun T hT =>
      timeTranslate_memLp_Ioc hs0 (hv.velocity_energy_class (T + s) (by linarith))
    gradient_energy_class := fun T hT =>
      timeTranslate_memLp_Ioc hs0 (hv.gradient_energy_class (T + s) (by linarith))
    initial := ?_
    weak_continuity := ?_
    strong_trace := lh_shifted_strong_trace_of_energy_start hv hν hs hE
    spatial_H1 := ?_
    dissipation_integrable := ?_
    energy_initial := ?_
    energy_intervals := ?_
  }
  · simpa only [timeTranslate, zero_add, criticalL2Representative_eq (v s) hvs]
      using hvs.coeFn_toLp.symm
  · intro φ hφ
    exact (hv.weak_continuity φ hφ).comp
      (continuous_id.add continuous_const).continuousOn
      (fun t ht => add_nonneg ht hs0)
  · intro T hT
    exact timeTranslate_ae_Ioc hs0 (hv.spatial_H1 (T + s) (by linarith))
  · intro T hT
    have hI := (hv.dissipation_integrable (T + s) (by linarith)).mono_set
      (show uIcc s (T + s) ⊆ uIcc (0 : ℝ) (T + s) by
        rw [uIcc_of_le (by linarith : s ≤ T + s),
          uIcc_of_le (by linarith : (0 : ℝ) ≤ T + s)]
        exact Icc_subset_Icc hs0 le_rfl)
    simpa only [sub_self, add_sub_cancel_right, timeTranslate]
      using hI.comp_add_right s
  · intro t ht
    change physicalEnergy (v (t + s)) +
      2 * ν * (∫ r in (0 : ℝ)..t, criticalGradientEnergy (G (r + s))) ≤ _
    rw [intervalIntegral.integral_comp_add_right, zero_add,
      restart_representative_norm_sq (v s) hvs]
    exact hE (t + s) (by linarith)
  · intro T hT
    have hE := timeTranslate_ae_Ioc hs0
      (hv.energy_intervals (T + s) (by linarith))
    filter_upwards [hE] with r hr
    intro t ht
    change physicalEnergy (v (t + s)) +
      2 * ν * (∫ q in r..t, criticalGradientEnergy (G (q + s))) ≤
        physicalEnergy (v (r + s))
    rw [intervalIntegral.integral_comp_add_right]
    exact hr (t + s) ⟨add_le_add_right ht.1 s, add_le_add_right ht.2 s⟩

theorem LH_RESTART_AT_GOOD_TIME
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν)
    {s : ℝ} (hs : LHGoodEnergyTime ν v G s) :
    CriticalLerayHopf ν (criticalL2Representative (v s))
      (timeTranslate s v) (timeTranslate s G) :=
  LH_RESTART_FROM_ENERGY_START hv hν hs.1.le hs.2.2

theorem LH_RESTART_AE
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      CriticalPhysicalH1 (v s) (G s) ∧
      CriticalLerayHopf ν (criticalL2Representative (v s))
        (timeTranslate s v) (timeTranslate s G) := by
  filter_upwards [lh_ae_good_energy_time hv] with s hs
  exact ⟨hs.2.1, LH_RESTART_AT_GOOD_TIME hv hν hs⟩

theorem LH_RESTART_AE_Ioc
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν) (T : ℝ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T),
      CriticalPhysicalH1 (v s) (G s) ∧
      CriticalLerayHopf ν (criticalL2Representative (v s))
        (timeTranslate s v) (timeTranslate s G) := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioi).mp (LH_RESTART_AE hv hν)
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [hglobal] with s hs
  intro hsT
  exact hs hsT.1

theorem LH_RESTART_AE_Ioo
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν) (T : ℝ) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) T),
      CriticalPhysicalH1 (v s) (G s) ∧
      CriticalLerayHopf ν (criticalL2Representative (v s))
        (timeTranslate s v) (timeTranslate s G) := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioi).mp (LH_RESTART_AE hv hν)
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hglobal] with s hs
  intro hsT
  exact hs hsT.1

end
end QuasiFeffermanB
