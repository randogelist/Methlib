import SingularClosure.HighOrderDiagonal

/-!
# Global continuous Sobolev curves from the actual common Galerkin subsequence

Compatible integer-horizon limits determine a literal function on nonnegative
time in every Sobolev order. The function is extended by zero to negative time.
Continuity follows locally from one horizon containing a neighborhood of the
time in question. No differential equation is asserted in this module.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace SingularClosure

noncomputable section

def globalSobolevCurve
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (r : ℕ) (t : ℝ) : TorusSobolev r :=
  if ht : 0 ≤ t then
    u (Nat.ceil t) r ⟨t, ht, (Nat.le_ceil t).trans (by linarith)⟩
  else 0

theorem globalSobolevCurve_eq_horizon
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (hoverlap : ∀ (m l r : ℕ) (t : ℝ)
      (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
      (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)),
      u m r ⟨t, hm⟩ = u l r ⟨t, hl⟩)
    (m r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1)) :
    globalSobolevCurve u r t = u m r ⟨t, ht⟩ := by
  simp only [globalSobolevCurve, dif_pos ht.1]
  exact hoverlap (Nat.ceil t) m r t _ ht

theorem globalSobolevCurve_continuousOn
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (hoverlap : ∀ (m l r : ℕ) (t : ℝ)
      (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
      (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)),
      u m r ⟨t, hm⟩ = u l r ⟨t, hl⟩)
    (r : ℕ) : ContinuousOn (globalSobolevCurve u r) (Ici 0) := by
  have hinterval (m : ℕ) : ContinuousOn (globalSobolevCurve u r)
      (Icc (0 : ℝ) ((m : ℝ) + 1)) := by
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun t : IntegerTimeHorizon m => globalSobolevCurve u r t.val)
    have heq : (fun t : IntegerTimeHorizon m => globalSobolevCurve u r t.val) =
        (u m r : IntegerTimeHorizon m → TorusSobolev r) := by
      funext t
      exact globalSobolevCurve_eq_horizon u hoverlap m r t.val t.property
    rw [heq]
    exact (u m r).continuous
  intro t ht
  have htlt : t < (Nat.ceil t : ℝ) + 1 := by
    have hceil := Nat.le_ceil t
    linarith
  have hc := hinterval (Nat.ceil t) t ⟨ht, htlt.le⟩
  apply hc.mono_of_mem_nhdsWithin
  apply mem_of_superset
    (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htlt)))
  intro s hs
  exact ⟨hs.1, hs.2.le⟩

theorem globalSobolevCurve_inclusion
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (hinclusion : ∀ (m r : ℕ) (t : IntegerTimeHorizon m),
      torusSobolevInclusion r (u m (r + 1) t) = u m r t)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    torusSobolevInclusion r (globalSobolevCurve u (r + 1) t) =
      globalSobolevCurve u r t := by
  simp only [globalSobolevCurve, dif_pos ht]
  exact hinclusion (Nat.ceil t) r _

theorem globalSobolevCurve_uniform_limit
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ∀ m r : ℕ, C(IntegerTimeHorizon m, TorusSobolev r))
    (φ : ℕ → ℕ)
    (hconv : ∀ m r, TendstoUniformly
      (fun n (t : IntegerTimeHorizon m) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      (u m r) atTop)
    (hoverlap : ∀ (m l r : ℕ) (t : ℝ)
      (hm : t ∈ Icc (0 : ℝ) ((m : ℝ) + 1))
      (hl : t ∈ Icc (0 : ℝ) ((l : ℝ) + 1)),
      u m r ⟨t, hm⟩ = u l r ⟨t, hl⟩)
    (T : ℝ) (r : ℕ) :
    TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t)
      (globalSobolevCurve u r) atTop (Icc (0 : ℝ) T) := by
  have hT : T ≤ (Nat.ceil T : ℝ) + 1 := (Nat.le_ceil T).trans (by linarith)
  let e : Icc (0 : ℝ) T → IntegerTimeHorizon (Nat.ceil T) :=
    fun t => ⟨t.val, t.property.1, t.property.2.trans hT⟩
  have h := (hconv (Nat.ceil T) r).comp e
  have heq : (fun t : Icc (0 : ℝ) T => u (Nat.ceil T) r (e t)) =
      (fun t => globalSobolevCurve u r t.val) := by
    funext t
    exact (globalSobolevCurve_eq_horizon u hoverlap (Nat.ceil T) r t.val
      ⟨t.property.1, t.property.2.trans hT⟩).symm
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  have h' : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t.val)
      (fun t => u (Nat.ceil T) r (e t)) atTop := by
    simpa only [Function.comp_def, e] using h
  rw [heq] at h'
  exact h'

/-- AX6 yields one actual global continuous curve in every Sobolev order,
with a common canonical Galerkin subsequence on every finite time interval. -/
theorem AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_CURVES (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ U : ∀ r : ℕ, ℝ → TorusSobolev r, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ r, ContinuousOn (U r) (Ici 0)) ∧
      (∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        torusSobolevInclusion r (U (r + 1) t) = U r t) ∧
      ∀ (T : ℝ) (r : ℕ), TendstoUniformlyOn
        (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t)
        (U r) atTop (Icc (0 : ℝ) T) := by
  obtain ⟨u, φ, hφ, hconv, hoverlap, hinclusion⟩ :=
    AX6_CANONICAL_GALERKIN_GLOBAL_Hm_SUBSEQUENCE hAX6 ν hν a ha
  exact ⟨globalSobolevCurve u, φ, hφ,
    globalSobolevCurve_continuousOn u hoverlap,
    globalSobolevCurve_inclusion u hinclusion,
    globalSobolevCurve_uniform_limit ν hν a ha u φ hconv hoverlap⟩

end

end SingularClosure
