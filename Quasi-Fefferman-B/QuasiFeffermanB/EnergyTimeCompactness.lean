import QuasiFeffermanB.EnergyGalerkinCompactness
import SingularClosure.CriticalLimitUniform
import SingularClosure.SobolevTimeL2Compactness
import SingularClosure.CriticalGalerkinTrajectory

/-! Actual strong L2-in-time energy compactness from finite-mode convergence
and the ordinary energy dissipation budget. No critical norm is assumed. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

abbrev EnergyTimeH0L2 (T : ℝ) :=
  Lp (TorusSobolev 0) 2 (volume.restrict (Icc (0 : ℝ) T))

theorem energyTimeH0L2_norm_sq (T : ℝ) (f : EnergyTimeH0L2 T) :
    ‖f‖ ^ 2 = ∫ t in Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  calc
    _ = (inner ℂ f f).re := (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
    _ = (∫ t in Icc (0 : ℝ) T, inner ℂ (f t) (f t)).re := by
      rw [L2.inner_def]
    _ = ∫ t in Icc (0 : ℝ) T, (inner ℂ (f t) (f t)).re :=
      (Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => inner_self_eq_norm_sq (𝕜 := ℂ) (f t))

theorem energy_H0_tail_sq (K : ℕ) (hK : 0 < K) (v : TorusSobolev 1) :
    ‖torusSobolevInclusion 0 v -
      torusSobolevCutoff 0 K (torusSobolevInclusion 0 v)‖ ^ 2 ≤
      4 * (K : ℝ)⁻¹ * ‖v‖ ^ 2 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hInv : 0 ≤ (K : ℝ)⁻¹ := inv_nonneg.mpr hKr.le
  have hInvOne : (K : ℝ)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hKr).mpr (by simpa using hKone)
  have hInvSq : ((K : ℝ)⁻¹) ^ 2 ≤ 4 * (K : ℝ)⁻¹ := by
    nlinarith
  have htail := pow_le_pow_left₀ (norm_nonneg _)
    (torusSobolevInclusion_tail 0 K hK v) 2
  rw [mul_pow] at htail
  exact htail.trans (mul_le_mul_of_nonneg_right hInvSq (sq_nonneg ‖v‖))

theorem _root_.SingularClosure.GalerkinSolution.energy_H0_time_tail
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (T B : ℝ) (hT : 0 ≤ T)
    (hbudget : (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t‖ ^ 2) ≤ B)
    (K : ℕ) (hK : 0 < K) :
    (∫ t in (0 : ℝ)..T,
      ‖g.sobolevState 0 t - torusSobolevCutoff 0 K (g.sobolevState 0 t)‖ ^ 2) ≤
      4 * (K : ℝ)⁻¹ * B := by
  have h0 : ContinuousOn (g.sobolevState 0) (Icc (0 : ℝ) T) :=
    (g.sobolevState_continuousOn 0).mono (fun t ht => ht.1)
  have h1 : ContinuousOn (g.sobolevState 1) (Icc (0 : ℝ) T) :=
    (g.sobolevState_continuousOn 1).mono (fun t ht => ht.1)
  have hp := (torusSobolevCutoff 0 K).continuous.comp_continuousOn h0
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, 4 * (K : ℝ)⁻¹ * ‖g.sobolevState 1 t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hT
        (((h0.sub hp).norm.pow 2).intervalIntegrable_of_Icc hT)
        (((h1.norm.pow 2).const_mul (4 * (K : ℝ)⁻¹)).intervalIntegrable_of_Icc hT)
      intro t ht
      change ‖g.sobolevState 0 t - torusSobolevCutoff 0 K (g.sobolevState 0 t)‖ ^ 2 ≤
        4 * (K : ℝ)⁻¹ * ‖g.sobolevState 1 t‖ ^ 2
      simpa only [GalerkinSolution.sobolevState_inclusion] using
        energy_H0_tail_sq K hK (g.sobolevState 1 t)
    _ = 4 * (K : ℝ)⁻¹ * (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

private theorem energy_norm_sub_three_parts
    {E : Type*} [NormedAddCommGroup E] (u v p q : E) :
    ‖u - v‖ ^ 2 ≤ 3 * ‖u - p‖ ^ 2 + 3 * ‖p - q‖ ^ 2 + 3 * ‖v - q‖ ^ 2 := by
  have heq : u - v = (u - p) + (p - q) + (q - v) := by abel
  have hnorm : ‖u - v‖ ≤ ‖u - p‖ + ‖p - q‖ + ‖v - q‖ := by
    rw [heq]
    calc
      _ ≤ ‖(u - p) + (p - q)‖ + ‖q - v‖ := norm_add_le _ _
      _ ≤ (‖u - p‖ + ‖p - q‖) + ‖q - v‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [norm_sub_rev q v]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_nonneg (‖u - p‖ - ‖p - q‖), sq_nonneg (‖u - p‖ - ‖v - q‖),
    sq_nonneg (‖p - q‖ - ‖v - q‖)]

/-- The high-frequency energy budget and the finite-band gap control the full time-H0 gap. -/
theorem energyGalerkin_H0_time_difference_bound
    {ν : ℝ} {a b : Field} {N M : ℕ}
    (g : GalerkinSolution ν a N) (h : GalerkinSolution ν b M)
    (T B η : ℝ) (hT : 0 ≤ T) (hη : 0 ≤ η)
    (hg : (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t‖ ^ 2) ≤ B)
    (hh : (∫ t in (0 : ℝ)..T, ‖h.sobolevState 1 t‖ ^ 2) ≤ B)
    (K : ℕ) (hK : 0 < K)
    (hgap : ∀ t ∈ Icc (0 : ℝ) T,
      ‖torusSobolevCutoff 0 K (g.sobolevState 0 t) -
        torusSobolevCutoff 0 K (h.sobolevState 0 t)‖ ≤ η) :
    (∫ t in (0 : ℝ)..T, ‖g.sobolevState 0 t - h.sobolevState 0 t‖ ^ 2) ≤
      24 * (K : ℝ)⁻¹ * B + 3 * T * η ^ 2 := by
  have hgcont : ContinuousOn (g.sobolevState 0) (Icc (0 : ℝ) T) :=
    (g.sobolevState_continuousOn 0).mono (fun t ht => ht.1)
  have hhcont : ContinuousOn (h.sobolevState 0) (Icc (0 : ℝ) T) :=
    (h.sobolevState_continuousOn 0).mono (fun t ht => ht.1)
  have hgp := (torusSobolevCutoff 0 K).continuous.comp_continuousOn hgcont
  have hhp := (torusSobolevCutoff 0 K).continuous.comp_continuousOn hhcont
  have hgi : IntervalIntegrable (fun t =>
      ‖g.sobolevState 0 t - torusSobolevCutoff 0 K (g.sobolevState 0 t)‖ ^ 2)
      volume 0 T := ((hgcont.sub hgp).norm.pow 2).intervalIntegrable_of_Icc hT
  have hhi : IntervalIntegrable (fun t =>
      ‖h.sobolevState 0 t - torusSobolevCutoff 0 K (h.sobolevState 0 t)‖ ^ 2)
      volume 0 T := ((hhcont.sub hhp).norm.pow 2).intervalIntegrable_of_Icc hT
  have hbound : (∫ t in (0 : ℝ)..T, ‖g.sobolevState 0 t - h.sobolevState 0 t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T,
        3 * ‖g.sobolevState 0 t - torusSobolevCutoff 0 K (g.sobolevState 0 t)‖ ^ 2 +
        3 * η ^ 2 +
        3 * ‖h.sobolevState 0 t - torusSobolevCutoff 0 K (h.sobolevState 0 t)‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on hT
      (((hgcont.sub hhcont).norm.pow 2).intervalIntegrable_of_Icc hT)
      (((hgi.const_mul 3).add intervalIntegrable_const).add (hhi.const_mul 3))
    intro t ht
    change ‖g.sobolevState 0 t - h.sobolevState 0 t‖ ^ 2 ≤
      3 * ‖g.sobolevState 0 t - torusSobolevCutoff 0 K (g.sobolevState 0 t)‖ ^ 2 +
      3 * η ^ 2 +
      3 * ‖h.sobolevState 0 t - torusSobolevCutoff 0 K (h.sobolevState 0 t)‖ ^ 2
    have hthree := energy_norm_sub_three_parts (g.sobolevState 0 t) (h.sobolevState 0 t)
      (torusSobolevCutoff 0 K (g.sobolevState 0 t))
      (torusSobolevCutoff 0 K (h.sobolevState 0 t))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hgap t ht) 2
    nlinarith
  rw [intervalIntegral.integral_add ((hgi.const_mul 3).add intervalIntegrable_const)
      (hhi.const_mul 3),
    intervalIntegral.integral_add (hgi.const_mul 3) intervalIntegrable_const] at hbound
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hbound
  have hgtail := g.energy_H0_time_tail T B hT hg K hK
  have hhtail := h.energy_H0_time_tail T B hT hh K hK
  nlinarith

def _root_.SingularClosure.GalerkinSolution.energyTimeH0L2 {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (T : ℝ) : EnergyTimeH0L2 T :=
  (g.sobolevState_memLp 0 T 2).toLp (g.sobolevState 0)

theorem energyTimeH0L2_sub_norm_sq
    {ν : ℝ} {a b : Field} {N M : ℕ}
    (g : GalerkinSolution ν a N) (h : GalerkinSolution ν b M)
    (T : ℝ) (hT : 0 ≤ T) :
    ‖g.energyTimeH0L2 T - h.energyTimeH0L2 T‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖g.sobolevState 0 t - h.sobolevState 0 t‖ ^ 2 := by
  rw [energyTimeH0L2_norm_sq]
  calc
    _ = ∫ t in Icc (0 : ℝ) T, ‖g.sobolevState 0 t - h.sobolevState 0 t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (g.energyTimeH0L2 T) (h.energyTimeH0L2 T),
        (g.sobolevState_memLp 0 T 2).coeFn_toLp,
        (h.sobolevState_memLp 0 T 2).coeFn_toLp] with t hsub hg hh
      rw [hsub]
      change ‖(g.sobolevState_memLp 0 T 2).toLp (g.sobolevState 0) t -
        (h.sobolevState_memLp 0 T 2).toLp (h.sobolevState 0) t‖ ^ 2 = _
      rw [hg, hh]
    _ = _ := by
      rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

theorem ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (u0 : Icc (0 : ℝ) T → TorusSobolev 0)
    (hconv : ∀ k i, TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
      ((g n).sobolevState 0 t.val).val k i) (fun t => (u0 t).val k i) atTop)
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).sobolevState 1 t‖ ^ 2) ≤ B) :
    ∃ u1 : EnergyTimeH0L2 T,
      Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 u1) := by
  have hcauchy : CauchySeq (fun n => (g n).energyTimeH0L2 T) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (48 * B / ε ^ 2)
    let J := K + 1
    have hJ : 0 < J := Nat.succ_pos K
    have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
    have hlarge : 48 * B < (J : ℝ) * ε ^ 2 := by
      have hKJ : (K : ℝ) < J := by dsimp [J]; norm_cast; omega
      exact (div_lt_iff₀ (sq_pos_of_pos hε)).mp (hK.trans hKJ)
    have htail : 24 * (J : ℝ)⁻¹ * B < ε ^ 2 / 2 := by
      have hdiv : 24 * B / (J : ℝ) < ε ^ 2 / 2 :=
        (div_lt_iff₀ hJr).mpr (by nlinarith)
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    let η := Real.sqrt (ε ^ 2 / (12 * (T + 1)))
    have hη : 0 < η := Real.sqrt_pos.mpr (by positivity)
    have hηsq : η ^ 2 = ε ^ 2 / (12 * (T + 1)) := Real.sq_sqrt (by positivity)
    have hheadsmall : 3 * T * η ^ 2 < ε ^ 2 / 2 := by
      rw [hηsq]
      have hden : 0 < 12 * (T + 1) := by positivity
      have heq : (ε ^ 2 / (12 * (T + 1))) * (12 * (T + 1)) = ε ^ 2 :=
        div_mul_cancel₀ _ hden.ne'
      have hnonneg : 0 ≤ ε ^ 2 / (12 * (T + 1)) := by positivity
      nlinarith [sq_pos_of_pos hε]
    have hlift := torusSobolevCutoff_tendstoUniformly_of_coeff 0 J
      (fun n (t : Icc (0 : ℝ) T) => (g n).sobolevState 0 t.val) u0 hconv
    obtain ⟨L, hL⟩ := eventually_atTop.mp
      (Metric.tendstoUniformly_iff.mp hlift (η / 2) (half_pos hη))
    refine ⟨L, ?_⟩
    intro m hm n hn
    have hgap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        ‖torusSobolevCutoff 0 J ((g m).sobolevState 0 t) -
          torusSobolevCutoff 0 J ((g n).sobolevState 0 t)‖ ≤ η := by
      have hm' := hL m hm ⟨t, ht⟩
      have hn' := hL n hn ⟨t, ht⟩
      change dist (torusSobolevCutoff 0 J (u0 ⟨t, ht⟩))
        (torusSobolevCutoff 0 J ((g m).sobolevState 0 t)) < η / 2 at hm'
      change dist (torusSobolevCutoff 0 J (u0 ⟨t, ht⟩))
        (torusSobolevCutoff 0 J ((g n).sobolevState 0 t)) < η / 2 at hn'
      rw [← dist_eq_norm]
      have htri := dist_triangle_left
        (torusSobolevCutoff 0 J ((g m).sobolevState 0 t))
        (torusSobolevCutoff 0 J ((g n).sobolevState 0 t))
        (torusSobolevCutoff 0 J (u0 ⟨t, ht⟩))
      linarith
    have hnumeric := energyGalerkin_H0_time_difference_bound (g m) (g n)
      T B η hT hη.le (hbudget m) (hbudget n) J hJ hgap
    rw [← energyTimeH0L2_sub_norm_sq (g m) (g n) T hT] at hnumeric
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
      (hnumeric.trans_lt (by linarith))
  exact cauchySeq_tendsto_of_complete hcauchy


end
end QuasiFeffermanB

