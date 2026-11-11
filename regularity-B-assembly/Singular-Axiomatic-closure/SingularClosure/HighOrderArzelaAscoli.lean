import SingularClosure.HighOrderTimeModulus
import SingularClosure.HighOrderAccumulation
import SingularClosure.CanonicalGalerkin
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

/-!
# Uniform finite-horizon compactness in every actual Sobolev order

The compact range in Hm follows from the proved H(m+1) accumulation bound
and the actual compact Sobolev inclusion. Equicontinuity follows from the
proved Hm time modulus. Every curve is the canonical Fourier-Galerkin path.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped Topology Interval BoundedContinuousFunction

namespace SingularClosure

noncomputable section

local instance compactHighOrderTimeInterval (T : ℝ) : CompactSpace (Icc (0 : ℝ) T) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

def canonicalHighOrderCurve (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (r n : ℕ) : C(Icc (0 : ℝ) T, TorusSobolev r) where
  toFun t := (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r t.val
  continuous_toFun := by
    exact ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_continuousOn r).comp_continuous
      continuous_subtype_val (fun t => t.property.1)

def canonicalHighOrderCurveBounded (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (r n : ℕ) : (Icc (0 : ℝ) T) →ᵇ TorusSobolev r :=
  BoundedContinuousFunction.mkOfCompact (canonicalHighOrderCurve ν hν a ha T r n)

@[simp]
theorem canonicalHighOrderCurveBounded_apply (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (r n : ℕ) (t : Icc (0 : ℝ) T) :
    canonicalHighOrderCurveBounded ν hν a ha T r n t =
      (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r t.val := rfl

/-- Actual finite-horizon canonical trajectories have compact closure in uniform Hm norm. -/
theorem AX6_CANONICAL_GALERKIN_Hm_COMPACT_CLOSURE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (r : ℕ) :
    IsCompact (closure (Set.range (canonicalHighOrderCurveBounded ν hν a ha T r))) := by
  obtain ⟨B, hB, hbound⟩ := AX6_UNIFORM_HIGH_ORDER_POINTWISE hAX6 ν hν a ha T hT (r + 1)
  obtain ⟨M, hM, hmod⟩ := AX6_UNIFORM_HIGH_ORDER_TIME_MODULUS hAX6 ν hν a ha T hT r
  let F : ℕ → (Icc (0 : ℝ) T) →ᵇ TorusSobolev r :=
    canonicalHighOrderCurveBounded ν hν a ha T r
  let K : Set (TorusSobolev r) := closure ((torusSobolevInclusion r) ''
    closedBall (0 : TorusSobolev (r + 1)) (B + 1))
  have hK : IsCompact K :=
    (torusSobolevInclusion_compact r).isCompact_closure_image_closedBall (B + 1)
  have hrange (n : ℕ) (t : Icc (0 : ℝ) T) : F n t ∈ K := by
    apply subset_closure
    refine ⟨(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState (r + 1) t.val, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hb := hbound (n + 1) (by omega)
        (canonicalGalerkinSolution ν hν a ha (n + 1)) t.val t.property
      nlinarith [sq_nonneg
        (‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState (r + 1) t.val‖ - 1)]
    · exact (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_inclusion r t.val
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
    have hb := hmod (n + 1) (by omega)
      (canonicalGalerkinSolution ν hν a ha (n + 1)) y.val y.property x.val x.property
    rw [dist_eq_norm]
    change ‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r x.val -
      (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r y.val‖ < ε
    nlinarith [abs_nonneg (x.val - y.val), norm_nonneg
      ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r x.val -
        (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState r y.val)]
  have hequi : Equicontinuous ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev r) := by
    have he : ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev r) =
        (fun f : Set.range F => fun t => F f.property.choose t) := by
      funext f t
      exact congrArg (fun q : (Icc (0 : ℝ) T) →ᵇ TorusSobolev r => q t)
        f.property.choose_spec.symm
    rw [he]
    exact huni.equicontinuous.comp (fun f : Set.range F => f.property.choose)
  have hcompact : IsCompact (closure (Set.range F)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (Set.range F)
      (by intro f t hf; obtain ⟨n, rfl⟩ := hf; exact hrange n t) hequi
  exact hcompact

/-- The actual canonical trajectories have a uniformly convergent Hm subsequence
on every finite time interval. The subsequence cutoff is exactly φ(n)+1. -/
theorem AX6_CANONICAL_GALERKIN_Hm_UNIFORM_SUBSEQUENCE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (r : ℕ) :
    ∃ u : C(Icc (0 : ℝ) T, TorusSobolev r), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
        u atTop := by
  let F : ℕ → (Icc (0 : ℝ) T) →ᵇ TorusSobolev r :=
    canonicalHighOrderCurveBounded ν hν a ha T r
  have hcompact : IsCompact (closure (Set.range F)) :=
    AX6_CANONICAL_GALERKIN_Hm_COMPACT_CLOSURE hAX6 ν hν a ha T hT r
  obtain ⟨u, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨u.toContinuousMap, φ, hφ, ?_⟩
  change TendstoUniformly (fun n t => F (φ n) t) (fun t => u t) atTop
  simpa only [Function.comp_def] using
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv)

end

end SingularClosure
