import SingularClosure.CriticalSpaces
import SingularClosure.CriticalGalerkin
import SingularClosure.GalerkinCoefficientCompactness
import SingularClosure.CountableCompactExtraction
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! Fourier compactness at the critical regularity.

The negative half-order derivative norm gives a separate temporal modulus for
each Fourier coordinate. Countable Arzela--Ascoli then selects one subsequence
for all coordinates. No uniform positive-order norm at the initial time is
required beyond the actual half-order state bound.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped Topology BigOperators Interval BoundedContinuousFunction

namespace SingularClosure

noncomputable section

local instance criticalCompactTimeInterval (T : ℝ) : CompactSpace (Icc (0 : ℝ) T) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Scalar compactness from a squared one-half-Holder time modulus. -/
theorem critical_complex_curve_precompact
    (T : ℝ) (F : ℕ → (Icc (0 : ℝ) T) →ᵇ ℂ)
    (R M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n t, ‖F n t‖ ≤ R)
    (hmod : ∀ n (s t : Icc (0 : ℝ) T),
      ‖F n t - F n s‖ ^ 2 ≤ M * |t.val - s.val|) :
    IsCompact (closure (Set.range F)) := by
  have huni : UniformEquicontinuous (fun n (t : Icc (0 : ℝ) T) => F n t) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε ^ 2 / (M + 1), div_pos (sq_pos_of_pos hε) (by linarith), ?_⟩
    intro x y hxy n
    change dist (x.val : ℝ) y.val < ε ^ 2 / (M + 1) at hxy
    rw [Real.dist_eq] at hxy
    have hsmall : (M + 1) * |x.val - y.val| < ε ^ 2 := by
      have h := (lt_div_iff₀ (by linarith : 0 < M + 1)).mp hxy
      simpa only [mul_comm] using h
    have hb := hmod n y x
    rw [dist_eq_norm]
    nlinarith [abs_nonneg (x.val - y.val), norm_nonneg (F n x - F n y)]
  have hequi : Equicontinuous ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → ℂ) := by
    have he : ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → ℂ) =
        (fun f : Set.range F => fun t => F f.property.choose t) := by
      funext f t
      exact congrArg (fun q : (Icc (0 : ℝ) T) →ᵇ ℂ => q t)
        f.property.choose_spec.symm
    rw [he]
    exact huni.equicontinuous.comp (fun f : Set.range F => f.property.choose)
  exact BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) R)
    (isCompact_closedBall 0 R) (Set.range F)
    (by
      intro f t hf
      obtain ⟨n, rfl⟩ := hf
      simpa only [mem_closedBall, dist_zero_right] using hbound n t) hequi

/-- A countable set of coefficient curves has one common uniform subsequence. -/
theorem critical_countable_coefficient_uniform_subsequence
    {ι : Type*} [Countable ι] (T : ℝ)
    (F : ι → ℕ → C(Icc (0 : ℝ) T, ℂ))
    (R M : ι → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbound : ∀ i n t, ‖F i n t‖ ≤ R i)
    (hmod : ∀ i n (s t : Icc (0 : ℝ) T),
      ‖F i n t - F i n s‖ ^ 2 ≤ M i * |t.val - s.val|) :
    ∃ u : ι → C(Icc (0 : ℝ) T, ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ i, TendstoUniformly (fun n t => F i (φ n) t) (u i) atTop := by
  let G : ι → ℕ → (Icc (0 : ℝ) T) →ᵇ ℂ :=
    fun i n => BoundedContinuousFunction.mkOfCompact (F i n)
  have hcompact : ∀ i, IsCompact (closure (Set.range (G i))) := by
    intro i
    exact critical_complex_curve_precompact T (G i) (R i) (M i) (hM i)
      (hbound i) (hmod i)
  obtain ⟨u, φ, hφ, hu⟩ := countable_precompact_family_subsequence G hcompact
  refine ⟨fun i => (u i).toContinuousMap, φ, hφ, ?_⟩
  intro i
  change TendstoUniformly (fun n t => G i (φ n) t) (fun t => u i t) atTop
  simpa only [Function.comp_def] using
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hu i))

/-- Actual coefficient evaluation is controlled by its weighted-space operator norm. -/
theorem criticalCoeff_norm_le (q : ℤ) (v : CriticalSobolev q)
    (k : Frequency) (i : Fin 3) :
    ‖criticalCoeff q v k i‖ ≤ ‖criticalSobolevCoeff q k i‖ * ‖v‖ := by
  simpa only [criticalSobolevCoeff_apply] using
    (criticalSobolevCoeff q k i).le_opNorm v

/-- The H^(-1/2) derivative budget controls each actual Galerkin mode increment. -/
theorem GalerkinSolution.critical_coefficient_time_modulus
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (D : ℝ → CriticalSobolev (-1)) (T B : ℝ) (hB : 0 ≤ B)
    (hD : ContinuousOn D (Icc (0 : ℝ) T))
    (hDcoeff : ∀ r ∈ Icc (0 : ℝ) T, ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      criticalCoeff (-1) (D r) k i = galerkinRhs ν N (g.coeff r) k i)
    (hbudget : (∫ r in (0 : ℝ)..T, ‖D r‖ ^ 2) ≤ B)
    (k : Frequency) (i : Fin 3) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖g.coeff t k i - g.coeff s k i‖ ^ 2 ≤
      (t - s) * (‖criticalSobolevCoeff (-1) k i‖ ^ 2 * B) := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hlen : 0 ≤ t - s := sub_nonneg.mpr hst
  let C : ℝ := ‖criticalSobolevCoeff (-1) k i‖ ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  by_cases hk : k ∈ cutoffModes N
  · have hrhs : ContinuousOn (fun r => galerkinRhs ν N (g.coeff r) k i) (Icc s t) :=
      (g.rhs_continuousOn hk i).mono (fun r hr => hs.trans hr.1)
    have hDlocal : ContinuousOn D (Icc s t) :=
      hD.mono (fun r hr => ⟨hs.trans hr.1, hr.2.trans htT⟩)
    have hlocal := intervalIntegral_norm_sq_le_length_mul_integral_norm_sq hst hrhs
    rw [g.coefficient_integral_rhs hk i hs hst] at hlocal
    have hcompare : (∫ r in s..t, ‖galerkinRhs ν N (g.coeff r) k i‖ ^ 2) ≤
        C * (∫ r in s..t, ‖D r‖ ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hst
        ((hrhs.norm.pow 2).intervalIntegrable_of_Icc hst)
        (((hDlocal.norm.pow 2).const_mul C).intervalIntegrable_of_Icc hst)
      intro r hr
      change ‖galerkinRhs ν N (g.coeff r) k i‖ ^ 2 ≤ C * ‖D r‖ ^ 2
      rw [← hDcoeff r ⟨hs.trans hr.1, hr.2.trans htT⟩ k hk i]
      have hn := pow_le_pow_left₀ (norm_nonneg _)
        (criticalCoeff_norm_le (-1) (D r) k i) 2
      simpa only [mul_pow] using hn
    have hfull : (∫ r in s..t, ‖D r‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..T, ‖D r‖ ^ 2 := by
      apply intervalIntegral.integral_mono_interval hs hst htT
      · exact Filter.Eventually.of_forall (fun r => sq_nonneg _)
      · exact (hD.norm.pow 2).intervalIntegrable_of_Icc hT
    exact hlocal.trans (mul_le_mul_of_nonneg_left
      (hcompare.trans (mul_le_mul_of_nonneg_left (hfull.trans hbudget) hC)) hlen)
  · rw [g.mode_support t (hs.trans hst) k hk i, g.mode_support s hs k hk i]
    simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg hlen (mul_nonneg hC hB)

/-- Critical norm bounds yield actual simultaneous Fourier compactness.
The physical initial datum may depend on the cutoff, as in rough-data approximation. -/
theorem CRITICAL_GALERKIN_COEFFICIENT_SUBSEQUENCE
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (U : ℕ → ℝ → CriticalSobolev 1) (D : ℕ → ℝ → CriticalSobolev (-1))
    (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUcoeff : ∀ n t, 0 ≤ t → criticalCoeff 1 (U n t) = (g n).coeff t)
    (hD : ∀ n, ContinuousOn (D n) (Icc (0 : ℝ) T))
    (hDcoeff : ∀ n t, t ∈ Icc (0 : ℝ) T → ∀ k ∈ cutoffModes (N n),
      ∀ i : Fin 3, criticalCoeff (-1) (D n t) k i =
        galerkinRhs ν (N n) ((g n).coeff t) k i)
    (hstate : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖U n t‖ ≤ A)
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖D n t‖ ^ 2) ≤ B) :
    ∃ u : FourierIndex → C(Icc (0 : ℝ) T, ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k i,
        TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
          (g (φ n)).coeff t.val k i) (u (k, i)) atTop := by
  let F : FourierIndex → ℕ → C(Icc (0 : ℝ) T, ℂ) := fun ki n =>
    ⟨fun t => (g n).coeff t.val ki.1 ki.2,
      ((g n).coefficient_continuous ki.1 ki.2).comp_continuous
        continuous_subtype_val (fun t => t.property.1)⟩
  let R : FourierIndex → ℝ := fun ki => ‖criticalSobolevCoeff 1 ki.1 ki.2‖ * A
  let M : FourierIndex → ℝ := fun ki => ‖criticalSobolevCoeff (-1) ki.1 ki.2‖ ^ 2 * B
  have hM (ki : FourierIndex) : 0 ≤ M ki := mul_nonneg (sq_nonneg _) hB
  have hbound (ki : FourierIndex) (n : ℕ) (t : Icc (0 : ℝ) T) :
      ‖F ki n t‖ ≤ R ki := by
    change ‖(g n).coeff t.val ki.1 ki.2‖ ≤ ‖criticalSobolevCoeff 1 ki.1 ki.2‖ * A
    rw [← hUcoeff n t.val t.property.1]
    exact (criticalCoeff_norm_le 1 (U n t.val) ki.1 ki.2).trans
      (mul_le_mul_of_nonneg_left (hstate n t.val t.property)
        (norm_nonneg (criticalSobolevCoeff 1 ki.1 ki.2)))
  have hmod (ki : FourierIndex) (n : ℕ) (s t : Icc (0 : ℝ) T) :
      ‖F ki n t - F ki n s‖ ^ 2 ≤ M ki * |t.val - s.val| := by
    have hordered {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyT : y ≤ T) :
        ‖(g n).coeff y ki.1 ki.2 - (g n).coeff x ki.1 ki.2‖ ^ 2 ≤
          (y - x) * M ki :=
      (g n).critical_coefficient_time_modulus (D n) T B hB (hD n)
        (hDcoeff n) (hbudget n) ki.1 ki.2 hx hxy hyT
    change ‖(g n).coeff t.val ki.1 ki.2 - (g n).coeff s.val ki.1 ki.2‖ ^ 2 ≤ _
    rcases le_total s.val t.val with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using
        hordered s.property.1 hst t.property.2
    · calc
        _ = ‖(g n).coeff s.val ki.1 ki.2 - (g n).coeff t.val ki.1 ki.2‖ ^ 2 := by
          rw [norm_sub_rev]
        _ ≤ (s.val - t.val) * M ki := hordered t.property.1 hts s.property.2
        _ = M ki * |t.val - s.val| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, mul_comm]
  obtain ⟨u, φ, hφ, hconv⟩ := critical_countable_coefficient_uniform_subsequence
    T F R M hM hbound hmod
  exact ⟨u, φ, hφ, fun k i => hconv (k, i)⟩

end

end SingularClosure
