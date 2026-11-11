import SingularClosure.SobolevTimeModulus
import SingularClosure.StrongSobolevRealization
import SingularClosure.CanonicalGalerkin
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

/-!
# A uniform H0 subsequence of the actual canonical Galerkin trajectories

The compact range follows from the proved H1 bound and the actual compact
Sobolev inclusion. Equicontinuity follows from the proved H0 time modulus.
No compactness or equicontinuity certificate is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter Metric
open scoped Topology BoundedContinuousFunction

namespace SingularClosure

noncomputable section

local instance compactTimeInterval (T : ℝ) : CompactSpace (Icc (0 : ℝ) T) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

def canonicalSobolevCurve (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (n : ℕ) : C(Icc (0 : ℝ) T, TorusSobolev 0) where
  toFun t := (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 t.val
  continuous_toFun := by
    exact ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_continuousOn 0).comp_continuous
      continuous_subtype_val (fun t => t.property.1)

def canonicalSobolevCurveBounded (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (n : ℕ) : (Icc (0 : ℝ) T) →ᵇ TorusSobolev 0 :=
  BoundedContinuousFunction.mkOfCompact (canonicalSobolevCurve ν hν a ha T n)

@[simp]
theorem canonicalSobolevCurveBounded_apply (ν : ℝ) (hν : 0 < ν) (a : Field)
    (ha : SmoothSigmaZero a) (T : ℝ) (n : ℕ) (t : Icc (0 : ℝ) T) :
    canonicalSobolevCurveBounded ν hν a ha T n t =
      (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 t.val := rfl

/-- The actual canonical trajectories have a uniformly convergent H0 subsequence
on every finite time interval. The subsequence cutoff is exactly φ(n)+1. -/
theorem AX6_CANONICAL_GALERKIN_H0_UNIFORM_SUBSEQUENCE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ u : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
        u atTop := by
  obtain ⟨B, hB, hbound⟩ := AX6_UNIFORM_SOBOLEV_NORM_BOUNDS hAX6 ν hν a ha T hT
  obtain ⟨M, hM, hmod⟩ := AX6_UNIFORM_H0_TIME_MODULUS hAX6 ν hν a ha T hT
  let F : ℕ → (Icc (0 : ℝ) T) →ᵇ TorusSobolev 0 :=
    canonicalSobolevCurveBounded ν hν a ha T
  let K : Set (TorusSobolev 0) := closure ((torusSobolevInclusion 0) ''
    closedBall (0 : TorusSobolev 1) (B + 1))
  have hK : IsCompact K :=
    (torusSobolevInclusion_compact 0).isCompact_closure_image_closedBall (B + 1)
  have hrange (n : ℕ) (t : Icc (0 : ℝ) T) : F n t ∈ K := by
    apply subset_closure
    refine ⟨(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t.val, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hb := (hbound (n + 1) (by omega)
        (canonicalGalerkinSolution ν hν a ha (n + 1))).1 t.val t.property
      nlinarith [sq_nonneg
        (‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t.val‖ - 1)]
    · exact (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_inclusion 0 t.val
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
    change ‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 x.val -
      (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 y.val‖ < ε
    nlinarith [abs_nonneg (x.val - y.val), norm_nonneg
      ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 x.val -
        (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 y.val)]
  have hequi : Equicontinuous ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev 0) := by
    have he : ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev 0) =
        (fun f : Set.range F => fun t => F f.property.choose t) := by
      funext f t
      exact congrArg (fun q : (Icc (0 : ℝ) T) →ᵇ TorusSobolev 0 => q t)
        f.property.choose_spec.symm
    rw [he]
    exact huni.equicontinuous.comp (fun f : Set.range F => f.property.choose)
  have hcompact : IsCompact (closure (Set.range F)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (Set.range F)
      (by intro f t hf; obtain ⟨n, rfl⟩ := hf; exact hrange n t) hequi
  obtain ⟨u, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨u.toContinuousMap, φ, hφ, ?_⟩
  change TendstoUniformly (fun n t => F (φ n) t) (fun t => u t) atTop
  simpa only [Function.comp_def] using
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv)

end

end SingularClosure
