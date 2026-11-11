import SingularClosure.SobolevArzelaAscoli
import SingularClosure.SobolevInterpolation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual L²-in-time H1 compactness of the canonical Galerkin subsequence

Uniform H0 convergence and the proved H2 time bound imply that the literal
H1-valued Galerkin paths are Cauchy in their Bochner L² space. Completeness
then supplies a strong L² H1 limit. The same subsequence retains its uniform
H0 convergence.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped Topology ENNReal Interval

namespace SingularClosure

noncomputable section

abbrev TimeH1L2 (T : ℝ) :=
  Lp (TorusSobolev 1) 2 (volume.restrict (Icc (0 : ℝ) T))

def canonicalSobolevTimeH1L2 (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (n : ℕ) : TimeH1L2 T :=
  ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_memLp 1 T 2).toLp
    ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1)

theorem timeH1L2_norm_sq (T : ℝ) (f : TimeH1L2 T) :
    ‖f‖ ^ 2 = ∫ t in Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  calc
    _ = (inner ℂ f f).re := by simp [inner_self_eq_norm_sq]
    _ = (∫ t in Icc (0 : ℝ) T, inner ℂ (f t) (f t)).re := by
      rw [L2.inner_def]
    _ = ∫ t in Icc (0 : ℝ) T, (inner ℂ (f t) (f t)).re :=
      (Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by simp only [inner_self_eq_norm_sq, Complex.ofReal_re]

theorem canonicalSobolevTimeH1L2_sub_norm_sq (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (hT : 0 ≤ T) (m n : ℕ) :
    ‖canonicalSobolevTimeH1L2 ν hν a ha T m -
      canonicalSobolevTimeH1L2 ν hν a ha T n‖ ^ 2 =
      ∫ t in (0 : ℝ)..T,
        ‖(canonicalGalerkinSolution ν hν a ha (m + 1)).sobolevState 1 t -
          (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t‖ ^ 2 := by
  rw [timeH1L2_norm_sq]
  have hm := ((canonicalGalerkinSolution ν hν a ha (m + 1)).sobolevState_memLp 1 T 2).coeFn_toLp
  have hn := ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_memLp 1 T 2).coeFn_toLp
  calc
    _ = ∫ t in Icc (0 : ℝ) T,
        ‖(canonicalGalerkinSolution ν hν a ha (m + 1)).sobolevState 1 t -
          (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (canonicalSobolevTimeH1L2 ν hν a ha T m)
        (canonicalSobolevTimeH1L2 ν hν a ha T n), hm, hn] with t hsub hm hn
      rw [hsub]
      change ‖((canonicalGalerkinSolution ν hν a ha (m + 1)).sobolevState_memLp 1 T 2).toLp
          ((canonicalGalerkinSolution ν hν a ha (m + 1)).sobolevState 1) t -
        ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_memLp 1 T 2).toLp
          ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1) t‖ ^ 2 = _
      rw [hm, hn]
    _ = _ := by
      rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

/-- The actual canonical paths admit simultaneous uniform H0 and strong time-L² H1 limits. -/
theorem AX6_CANONICAL_GALERKIN_H0_L2H1_SUBSEQUENCE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ u0 : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ u1 : TimeH1L2 T,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly
          (fun n (t : Icc (0 : ℝ) T) =>
            (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
          u0 atTop ∧
        Tendsto (fun n => canonicalSobolevTimeH1L2 ν hν a ha T (φ n)) atTop (𝓝 u1) := by
  obtain ⟨u0, φ, hφ, hconv⟩ :=
    AX6_CANONICAL_GALERKIN_H0_UNIFORM_SUBSEQUENCE hAX6 ν hν a ha T hT
  obtain ⟨B, hB, hbound⟩ := AX6_UNIFORM_SOBOLEV_NORM_BOUNDS hAX6 ν hν a ha T hT
  have hcauchy : CauchySeq (fun n => canonicalSobolevTimeH1L2 ν hν a ha T (φ n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let A : ℝ := 4 * T * B
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let δ : ℝ := ε ^ 2 / (A + 1)
    have hden : 0 < A + 1 := by linarith
    have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
    have hδeq : δ * (A + 1) = ε ^ 2 := div_mul_cancel₀ _ hden.ne'
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (Metric.tendstoUniformly_iff.mp hconv (δ / 2) (half_pos hδ))
    refine ⟨N, ?_⟩
    intro m hm n hn
    let gm := canonicalGalerkinSolution ν hν a ha (φ m + 1)
    let gn := canonicalGalerkinSolution ν hν a ha (φ n + 1)
    have hgap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        ‖gm.sobolevState 0 t - gn.sobolevState 0 t‖ ≤ δ := by
      have hmt : dist (gm.sobolevState 0 t) (u0 ⟨t, ht⟩) < δ / 2 := by
        simpa only [dist_comm] using hN m hm ⟨t, ht⟩
      have hnt : dist (gn.sobolevState 0 t) (u0 ⟨t, ht⟩) < δ / 2 := by
        simpa only [dist_comm] using hN n hn ⟨t, ht⟩
      calc
        _ = dist (gm.sobolevState 0 t) (gn.sobolevState 0 t) := (dist_eq_norm _ _).symm
        _ ≤ dist (gm.sobolevState 0 t) (u0 ⟨t, ht⟩) +
            dist (gn.sobolevState 0 t) (u0 ⟨t, ht⟩) := dist_triangle_right _ _ _
        _ ≤ δ := by linarith
    have hgm : ContinuousOn (gm.sobolevState 2) (Icc (0 : ℝ) T) :=
      (gm.sobolevState_continuousOn 2).mono (fun t ht => ht.1)
    have hgn : ContinuousOn (gn.sobolevState 2) (Icc (0 : ℝ) T) :=
      (gn.sobolevState_continuousOn 2).mono (fun t ht => ht.1)
    have hgm2 := (hbound (φ m + 1) (by omega) gm).2.2.1
    have hgn2 := (hbound (φ n + 1) (by omega) gn).2.2.1
    have hinterp := torusSobolev_H1_time_difference_bound
      (gm.sobolevState 2) (gn.sobolevState 2) T δ B hT.le hδ.le hgm hgn
      (fun t ht => by simpa only [GalerkinSolution.sobolevState_inclusion] using hgap t ht)
      hgm2 hgn2
    simp only [GalerkinSolution.sobolevState_inclusion] at hinterp
    change (∫ t in (0 : ℝ)..T,
      ‖(canonicalGalerkinSolution ν hν a ha (φ m + 1)).sobolevState 1 t -
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 1 t‖ ^ 2) ^ 2 ≤ _ at hinterp
    rw [← canonicalSobolevTimeH1L2_sub_norm_sq ν hν a ha T hT.le (φ m) (φ n)] at hinterp
    have hcoef : 4 * δ ^ 2 * T * B < (ε ^ 2) ^ 2 := by
      have hfac : A < (A + 1) ^ 2 := by nlinarith [sq_nonneg A]
      calc
        _ = A * δ ^ 2 := by dsimp [A]; ring
        _ < (A + 1) ^ 2 * δ ^ 2 := mul_lt_mul_of_pos_right hfac (sq_pos_of_pos hδ)
        _ = (δ * (A + 1)) ^ 2 := by ring
        _ = _ := by rw [hδeq]
    have hfour := lt_of_le_of_lt hinterp hcoef
    have hsq := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mp hfour
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
  obtain ⟨u1, hu1⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨u0, u1, φ, hφ, hconv, hu1⟩

end

end SingularClosure
