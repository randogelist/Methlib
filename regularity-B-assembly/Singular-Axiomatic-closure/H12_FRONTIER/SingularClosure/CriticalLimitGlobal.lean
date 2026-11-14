import SingularClosure.CriticalLimitTimeL2

/-! A single rough-data Galerkin subsequence on all finite time horizons.

The diagonal is taken over horizon-frequency pairs. Coincidence on overlapping
intervals follows from uniqueness of scalar limits, without invoking solution
uniqueness. The resulting global path is bounded in Hhalf, continuous in H0,
and has a strong L2 H1 limit on every finite interval.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped BigOperators Topology Interval BoundedContinuousFunction

namespace SingularClosure

noncomputable section

local instance criticalGlobalCompactTime (m : ℕ) :
    CompactSpace (Icc (0 : ℝ) ((m : ℝ) + 1)) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- One countable diagonal gives uniform convergence of every Fourier coordinate
on every integer horizon. -/
theorem CRITICAL_GALERKIN_INTEGER_HORIZON_DIAGONAL
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hstate : ∀ n t, 0 ≤ t → ‖(g n).criticalState 1 t‖ ≤ A)
    (htime : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ c : ∀ m : ℕ, FourierIndex → C(Icc (0 : ℝ) ((m : ℝ) + 1), ℂ),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ (m : ℕ) (k : Frequency) (i : Fin 3), TendstoUniformly
          (fun n (t : Icc (0 : ℝ) ((m : ℝ) + 1)) => (g (φ n)).coeff t.val k i)
          (c m (k, i)) atTop) ∧
        ∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
          (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
          (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)),
          c m ki ⟨t, hm⟩ = c l ki ⟨t, hl⟩ := by
  let F : (p : ℕ × FourierIndex) → ℕ →
      (Icc (0 : ℝ) ((p.1 : ℝ) + 1)) →ᵇ ℂ := fun p n =>
    BoundedContinuousFunction.mkOfCompact
      (⟨fun t => (g n).coeff t.val p.2.1 p.2.2,
        ((g n).coefficient_continuous p.2.1 p.2.2).comp_continuous
          continuous_subtype_val (fun t => t.property.1)⟩ :
        C(Icc (0 : ℝ) ((p.1 : ℝ) + 1), ℂ))
  have hcompact (p : ℕ × FourierIndex) : IsCompact (closure (range (F p))) := by
    let C := ‖criticalSobolevCoeff (-1) p.2.1 p.2.2‖ ^ 2 * D
    apply critical_complex_curve_precompact ((p.1 : ℝ) + 1) (F p)
      (‖criticalSobolevCoeff 1 p.2.1 p.2.2‖ * A) C
      (mul_nonneg (sq_nonneg _) hD)
    · intro n t
      change ‖(g n).coeff t.val p.2.1 p.2.2‖ ≤ _
      rw [← (g n).criticalState_coeff 1 t.property.1]
      exact (criticalCoeff_norm_le 1 ((g n).criticalState 1 t.val) p.2.1 p.2.2).trans
        (mul_le_mul_of_nonneg_left (hstate n t.val t.property.1)
          (norm_nonneg (criticalSobolevCoeff 1 p.2.1 p.2.2)))
    · intro n s t
      have hord {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ (p.1 : ℝ) + 1) :
          ‖(g n).coeff y p.2.1 p.2.2 - (g n).coeff x p.2.1 p.2.2‖ ^ 2 ≤ (y - x) * C := by
        apply (g n).critical_coefficient_time_modulus ((g n).criticalRhs (-1))
          ((p.1 : ℝ) + 1) D hD
          (((g n).criticalRhs_continuousOn (-1)).mono (fun r hr => hr.1))
          (fun r hr k hk i => (g n).criticalRhs_coeff (-1) r hr.1 hk i)
          (htime n ((p.1 : ℝ) + 1) (by positivity)) p.2.1 p.2.2 hx hxy hy
      change ‖(g n).coeff t.val p.2.1 p.2.2 - (g n).coeff s.val p.2.1 p.2.2‖ ^ 2 ≤ _
      rcases le_total s.val t.val with hst | hts
      · simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using
          hord s.property.1 hst t.property.2
      · calc
          _ = ‖(g n).coeff s.val p.2.1 p.2.2 - (g n).coeff t.val p.2.1 p.2.2‖ ^ 2 := by
            rw [norm_sub_rev]
          _ ≤ (s.val - t.val) * C := hord t.property.1 hts s.property.2
          _ = C * |t.val - s.val| := by
            rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, mul_comm]
  obtain ⟨v, φ, hφ, hv⟩ := countable_precompact_family_subsequence F hcompact
  let c : ∀ m : ℕ, FourierIndex → C(Icc (0 : ℝ) ((m : ℝ) + 1), ℂ) :=
    fun m ki => (v (m, ki)).toContinuousMap
  have hconv (m : ℕ) (k : Frequency) (i : Fin 3) : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) ((m : ℝ) + 1)) => (g (φ n)).coeff t.val k i)
      (c m (k, i)) atTop := by
    change TendstoUniformly (fun n t => F (m, (k, i)) (φ n) t)
      (fun t => v (m, (k, i)) t) atTop
    simpa only [Function.comp_def] using
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hv (m, (k, i))))
  refine ⟨c, φ, hφ, hconv, ?_⟩
  intro m l ki t hm hl
  exact tendsto_nhds_unique ((hconv m ki.1 ki.2).tendsto_at ⟨t, hm⟩)
    ((hconv l ki.1 ki.2).tendsto_at ⟨t, hl⟩)

def criticalGlobalCoefficientCurve
    (c : ∀ m : ℕ, FourierIndex → C(Icc (0 : ℝ) ((m : ℝ) + 1), ℂ))
    (t : ℝ) : FourierCoeff :=
  if ht : 0 ≤ t then
    fun k i => c (Nat.ceil t) (k, i) ⟨t, ht, (Nat.le_ceil t).trans (by linarith)⟩
  else 0

theorem criticalGlobalCoefficientCurve_eq_horizon
    (c : ∀ m : ℕ, FourierIndex → C(Icc (0 : ℝ) ((m : ℝ) + 1), ℂ))
    (hoverlap : ∀ (m l : ℕ) (ki : FourierIndex) (t : ℝ)
      (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
      (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)), c m ki ⟨t, hm⟩ = c l ki ⟨t, hl⟩)
    (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
    (k : Frequency) (i : Fin 3) :
    criticalGlobalCoefficientCurve c t k i = c m (k, i) ⟨t, ht⟩ := by
  simp only [criticalGlobalCoefficientCurve, dif_pos ht.1]
  exact hoverlap (Nat.ceil t) m (k, i) t _ ht

theorem CRITICAL_GALERKIN_GLOBAL_COEFFICIENT_SUBSEQUENCE
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hstate : ∀ n t, 0 ≤ t → ‖(g n).criticalState 1 t‖ ≤ A)
    (htime : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ c : ℝ → FourierCoeff, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ (T : ℝ) (k : Frequency) (i : Fin 3), TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i)
        (fun t => c t.val k i) atTop := by
  obtain ⟨c, φ, hφ, hconv, hoverlap⟩ :=
    CRITICAL_GALERKIN_INTEGER_HORIZON_DIAGONAL ν a N g A D hA hD hstate htime
  refine ⟨criticalGlobalCoefficientCurve c, φ, hφ, ?_⟩
  intro T k i
  have hT : T ≤ (Nat.ceil T : ℝ) + 1 := (Nat.le_ceil T).trans (by linarith)
  let e : Icc (0 : ℝ) T → Icc (0 : ℝ) ((Nat.ceil T : ℝ) + 1) :=
    fun t => ⟨t.val, t.property.1, t.property.2.trans hT⟩
  have h := (hconv (Nat.ceil T) k i).comp e
  have heq : (fun t : Icc (0 : ℝ) T => c (Nat.ceil T) (k, i) (e t)) =
      (fun t => criticalGlobalCoefficientCurve c t.val k i) := by
    funext t
    exact (criticalGlobalCoefficientCurve_eq_horizon c hoverlap (Nat.ceil T) t.val
      ⟨t.property.1, t.property.2.trans hT⟩ k i).symm
  have h' : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i)
      (fun t => c (Nat.ceil T) (k, i) (e t)) atTop := by
    simpa only [Function.comp_def, e] using h
  rw [heq] at h'
  exact h'

/-- Actual global rough compactness from the three uniform critical estimates. -/
theorem CRITICAL_GALERKIN_GLOBAL_COMPACTNESS
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hstate : ∀ n t, 0 ≤ t → ‖(g n).criticalState 1 t‖ ≤ A)
    (hspace : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ A) ∧
      ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0) ∧
      (∀ T : ℝ, TendstoUniformlyOn
        (fun n t => (g (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ u1 : TimeH1L2 T,
        Tendsto (fun n => (g (φ n)).criticalTimeH1L2 T) atTop (𝓝 u1) := by
  classical
  obtain ⟨c, φ, hφ, hconv⟩ :=
    CRITICAL_GALERKIN_GLOBAL_COEFFICIENT_SUBSEQUENCE ν a N g A D hA hD hstate htime
  have hex (t : ℝ) (ht : 0 ≤ t) : ∃ v : CriticalSobolev 1,
      criticalCoeff 1 v = c t ∧ ‖v‖ ≤ A := by
    apply criticalSobolev_limit_mem_and_norm_le (l := (atTop : Filter ℕ)) 1
      (fun n => (g (φ n)).criticalState 1 t) (c t) A
    · intro n
      exact hstate (φ n) t ht
    · intro k i
      have heq (n : ℕ) : criticalCoeff 1 ((g (φ n)).criticalState 1 t) =
          (g (φ n)).coeff t := (g (φ n)).criticalState_coeff 1 ht
      simpa only [heq] using (hconv (t + 1) k i).tendsto_at ⟨t, ht, by linarith⟩
  let u : ℝ → CriticalSobolev 1 := fun t => if ht : 0 ≤ t then (hex t ht).choose else 0
  have hucoeff (t : ℝ) (ht : 0 ≤ t) : criticalCoeff 1 (u t) = c t := by
    change criticalCoeff 1 (if ht : 0 ≤ t then (hex t ht).choose else 0) = c t
    rw [dif_pos ht]
    exact (hex t ht).choose_spec.1
  have hubound (t : ℝ) (ht : 0 ≤ t) : ‖u t‖ ≤ A := by
    change @norm (CriticalSobolev 1) inferInstance
      (if ht : 0 ≤ t then (hex t ht).choose else 0) ≤ A
    rw [dif_pos ht]
    exact (hex t ht).choose_spec.2
  have hfinal (T : ℝ) : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).sobolevState 0 t.val)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t.val)) atTop := by
    have hcoeff' (k : Frequency) (i : Fin 3) : TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => criticalCoeff 1 ((g (φ n)).criticalState 1 t.val) k i)
        (fun t => criticalCoeff 1 (u t.val) k i) atTop := by
      have heq : (fun n (t : Icc (0 : ℝ) T) => criticalCoeff 1 ((g (φ n)).criticalState 1 t.val) k i) =
          (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i) := by
        funext n t
        rw [(g (φ n)).criticalState_coeff 1 t.property.1]
      have heq' : (fun t : Icc (0 : ℝ) T => criticalCoeff 1 (u t.val) k i) =
          (fun t => c t.val k i) := by
        funext t
        rw [hucoeff t.val t.property.1]
      rw [heq, heq']
      exact hconv T k i
    have h := critical_half_uniform_H0_of_coeff_uniform
      (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).criticalState 1 t.val)
      (fun t => u t.val) A hA (fun n t => hstate (φ n) t.val t.property.1)
      (fun t => hubound t.val t.property.1) hcoeff'
    have heq (n : ℕ) (t : Icc (0 : ℝ) T) :
        criticalToTorusH0 1 (by norm_num) ((g (φ n)).criticalState 1 t.val) =
        (g (φ n)).sobolevState 0 t.val := by
      apply Subtype.ext
      rw [criticalToTorusH0_coeff, (g (φ n)).criticalState_coeff 1 t.property.1,
        (g (φ n)).sobolevState_coeff 0 t.property.1]
    simpa only [heq] using h
  have huniform (T : ℝ) : TendstoUniformlyOn
      (fun n t => (g (φ n)).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr (hfinal T)
  have hcontinuous : ContinuousOn
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0) := by
    intro t ht
    change 0 ≤ t at ht
    have hi := (huniform (t + 1)).continuousOn ((Filter.Eventually.of_forall
      (fun n => ((g (φ n)).sobolevState_continuousOn 0).mono (fun z hz => hz.1))).frequently)
    have hc := hi t ⟨ht, by linarith⟩
    apply hc.mono_of_mem_nhdsWithin
    apply mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith : t < t + 1))))
    intro z hz
    exact ⟨hz.1, hz.2.le⟩
  refine ⟨u, φ, hφ, hubound, hcontinuous, huniform, ?_⟩
  intro T hT
  exact CRITICAL_GALERKIN_L2H1_LIMIT_OF_H0_UNIFORM ν (fun n => a (φ n))
    (fun n => N (φ n)) (fun n => g (φ n)) T B hT hB
    (fun t => criticalToTorusH0 1 (by norm_num) (u t.val)) (hfinal T)
    (fun n => hspace (φ n) T hT)

end

end SingularClosure
