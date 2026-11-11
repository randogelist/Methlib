import SingularClosure.CountableCompactExtraction
import SingularClosure.HighOrderArzelaAscoli

/-!
# A common Galerkin subsequence on all finite horizons and Sobolev orders

The compactness premise of countable extraction is discharged by the actual
canonical Galerkin compact-closure theorem at every integer horizon and order.
The same subsequence determines all limits; uniqueness of limits proves both
overlap compatibility and compatibility with the actual Sobolev inclusions.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace SingularClosure

noncomputable section

abbrev IntegerTimeHorizon (m : ℕ) := Icc (0 : ℝ) ((m : ℝ) + 1)

/-- Limits of the same canonical sequence agree at every common time. -/
theorem canonicalHighOrderLimits_overlap
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (φ : ℕ → ℕ)
    (hconv : ∀ m r, TendstoUniformly
      (fun n (t : IntegerTimeHorizon m) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      (u m r) atTop)
    (m l r : ℕ) (t : ℝ)
    (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
    (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)) :
    u m r ⟨t, hm⟩ = u l r ⟨t, hl⟩ := by
  exact tendsto_nhds_unique ((hconv m r).tendsto_at ⟨t, hm⟩)
    ((hconv l r).tendsto_at ⟨t, hl⟩)

/-- Adjacent Sobolev limits represent the same actual Fourier coefficients. -/
theorem canonicalHighOrderLimits_inclusion
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (φ : ℕ → ℕ)
    (hconv : ∀ m r, TendstoUniformly
      (fun n (t : IntegerTimeHorizon m) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      (u m r) atTop)
    (m r : ℕ) (t : IntegerTimeHorizon m) :
    torusSobolevInclusion r (u m (r + 1) t) = u m r t := by
  have hmap := (torusSobolevInclusion r).continuous.continuousAt.tendsto.comp
    ((hconv m (r + 1)).tendsto_at t)
  have hmap' : Tendsto
      (fun n => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      atTop (𝓝 (torusSobolevInclusion r (u m (r + 1) t))) := by
    simpa only [Function.comp_def, GalerkinSolution.sobolevState_inclusion] using hmap
  exact tendsto_nhds_unique hmap' ((hconv m r).tendsto_at t)

/-- One strictly increasing cutoff sequence converges in every Sobolev norm
on every integer time horizon, with all overlap and inclusion identities. -/
theorem AX6_CANONICAL_GALERKIN_GLOBAL_Hm_SUBSEQUENCE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ m r, TendstoUniformly
        (fun n (t : IntegerTimeHorizon m) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
        (u m r) atTop) ∧
      (∀ (m l r : ℕ) (t : ℝ)
        (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
        (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)),
        u m r ⟨t, hm⟩ = u l r ⟨t, hl⟩) ∧
      ∀ (m r : ℕ) (t : IntegerTimeHorizon m),
        torusSobolevInclusion r (u m (r + 1) t) = u m r t := by
  let E : ℕ × ℕ → Type := fun q => IntegerTimeHorizon q.1 →ᵇ TorusSobolev q.2
  let F : ∀ q, ℕ → E q := fun q =>
    canonicalHighOrderCurveBounded ν hν a ha ((q.1 : ℝ) + 1) q.2
  have hcompact (q : ℕ × ℕ) : IsCompact (closure (Set.range (F q))) :=
    AX6_CANONICAL_GALERKIN_Hm_COMPACT_CLOSURE hAX6 ν hν a ha
      ((q.1 : ℝ) + 1) (by positivity) q.2
  obtain ⟨v, φ, hφ, hv⟩ := countable_precompact_family_subsequence F hcompact
  let u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r) :=
    fun m r => (v (m, r)).toContinuousMap
  have hu (m r : ℕ) : TendstoUniformly
      (fun n (t : IntegerTimeHorizon m) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      (u m r) atTop := by
    change TendstoUniformly (fun n t => F (m, r) (φ n) t)
      (fun t => v (m, r) t) atTop
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hv (m, r))
  exact ⟨u, φ, hφ, hu,
    canonicalHighOrderLimits_overlap ν hν a ha u φ hu,
    canonicalHighOrderLimits_inclusion ν hν a ha u φ hu⟩

end

end SingularClosure
