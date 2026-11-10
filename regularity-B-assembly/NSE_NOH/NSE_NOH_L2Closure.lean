import NSE_NOH_L2Pullback
import Mathlib.Topology.MetricSpace.Isometry

/-!
NSE_NOH FIX17 — Closed-range factorization for arbitrary rough L² planar traces.

This is an unconditional topological edge conditional only on actual Mathlib
L² measure spaces: the scalar and planar-vector isometric pullbacks from FIX16
have closed range. Consequently a 3D L² limit of pulled-back 2D L² functions
has a unique planar preimage, and the preimages converge in L².

The input `a ∈ closure (range pullback)` is an approximation premise. The still
OPEN Fourier/distribution theorem must derive that premise from the frozen
WeakX1Invariant 3 a. No 2D NSE existence, passive smoothing, or unique 3D
Leray-Hopf evolution is claimed here.

NO_LOCAL_LEAN. Native Windows Lean 4.33.0 with cached Mathlib and theorem-level
external theorem-level dependency review required before promotion.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace NSE_NOH
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev ScalarL2Three := Lp ℝ (2 : ℝ≥0∞) (volume : Measure (Torus 3))
abbrev PlanarL2Three := Lp (Vector 2) (2 : ℝ≥0∞) (volume : Measure (Torus 3))

/-! Closedness follows from completeness of planar L² and the isometry. -/
theorem scalarL2Pullback_closedRange :
    IsClosed (Set.range scalarL2Pullback) := by
  exact scalarL2Pullback.isometry.isClosedEmbedding.isClosed_range

theorem planarL2Pullback_closedRange :
    IsClosed (Set.range planarL2Pullback) := by
  exact planarL2Pullback.isometry.isClosedEmbedding.isClosed_range

/-! Closeness in L² suffices for existence of a unique planar preimage. -/
theorem scalarL2Pullback_closure_iff (a : ScalarL2Three) :
    a ∈ closure (Set.range scalarL2Pullback) ↔
      ∃ w : L2Scalar2, scalarL2Pullback w = a := by
  rw [scalarL2Pullback_closedRange.closure_eq]
  simp only [Set.mem_range]

theorem planarL2Pullback_closure_iff (a : PlanarL2Three) :
    a ∈ closure (Set.range planarL2Pullback) ↔
      ∃ v : L2Vector 2, planarL2Pullback v = a := by
  rw [planarL2Pullback_closedRange.closure_eq]
  simp only [Set.mem_range]

theorem scalarL2Pullback_uniqueFactorization (a : ScalarL2Three)
    (h : a ∈ closure (Set.range scalarL2Pullback)) :
    ∃! w : L2Scalar2, scalarL2Pullback w = a := by
  obtain ⟨w, hw⟩ := (scalarL2Pullback_closure_iff a).mp h
  refine ⟨w, hw, ?_⟩
  intro z hz
  exact scalarL2Pullback_injective (hz.trans hw.symm)

theorem planarL2Pullback_uniqueFactorization (a : PlanarL2Three)
    (h : a ∈ closure (Set.range planarL2Pullback)) :
    ∃! v : L2Vector 2, planarL2Pullback v = a := by
  obtain ⟨v, hv⟩ := (planarL2Pullback_closure_iff a).mp h
  refine ⟨v, hv, ?_⟩
  intro z hz
  exact planarL2Pullback_injective (hz.trans hv.symm)

/-! A genuinely quantitative approximation hypothesis implies exact factorization. -/
theorem scalarL2Pullback_approximationFactorization (a : ScalarL2Three)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ w : L2Scalar2, dist a (scalarL2Pullback w) < ε) :
    ∃! w : L2Scalar2, scalarL2Pullback w = a := by
  apply scalarL2Pullback_uniqueFactorization a
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨w, hw⟩ := happrox ε hε
  exact ⟨scalarL2Pullback w, ⟨w, rfl⟩, hw⟩

theorem planarL2Pullback_approximationFactorization (a : PlanarL2Three)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ v : L2Vector 2, dist a (planarL2Pullback v) < ε) :
    ∃! v : L2Vector 2, planarL2Pullback v = a := by
  apply planarL2Pullback_uniqueFactorization a
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, hv⟩ := happrox ε hε
  exact ⟨planarL2Pullback v, ⟨v, rfl⟩, hv⟩

/-! The isometry reflects as well as preserves convergence. -/
theorem scalarL2Pullback_tendsto_iff
    {ι : Type*} (w : ι → L2Scalar2) (l : Filter ι) (w₀ : L2Scalar2) :
    Tendsto w l (𝓝 w₀) ↔
      Tendsto (fun i => scalarL2Pullback (w i)) l (𝓝 (scalarL2Pullback w₀)) := by
  simpa only [Function.comp_def] using
    (scalarL2Pullback.isometry.tendsto_nhds_iff (g := w) (a := l) (b := w₀))

theorem planarL2Pullback_tendsto_iff
    {ι : Type*} (v : ι → L2Vector 2) (l : Filter ι) (v₀ : L2Vector 2) :
    Tendsto v l (𝓝 v₀) ↔
      Tendsto (fun i => planarL2Pullback (v i)) l (𝓝 (planarL2Pullback v₀)) := by
  simpa only [Function.comp_def] using
    (planarL2Pullback.isometry.tendsto_nhds_iff (g := v) (a := l) (b := v₀))

/-! A strong L² limit of planar lifts factors, and planar data converge. -/
theorem scalarL2Pullback_limitFactorization
    (w : ℕ → L2Scalar2) (a : ScalarL2Three)
    (h : Tendsto (fun n => scalarL2Pullback (w n)) atTop (𝓝 a)) :
    ∃ w₀ : L2Scalar2,
      scalarL2Pullback w₀ = a ∧ Tendsto w atTop (𝓝 w₀) := by
  have hmem : ∀ᶠ n : ℕ in atTop,
      scalarL2Pullback (w n) ∈ Set.range scalarL2Pullback :=
    Filter.Eventually.of_forall (fun n : ℕ => ⟨w n, rfl⟩)
  have ha : a ∈ Set.range scalarL2Pullback :=
    scalarL2Pullback_closedRange.mem_of_tendsto h hmem
  obtain ⟨w₀, hw₀⟩ := ha
  refine ⟨w₀, hw₀, ?_⟩
  apply (scalarL2Pullback_tendsto_iff w atTop w₀).mpr
  simpa only [hw₀] using h

theorem planarL2Pullback_limitFactorization
    (v : ℕ → L2Vector 2) (a : PlanarL2Three)
    (h : Tendsto (fun n => planarL2Pullback (v n)) atTop (𝓝 a)) :
    ∃ v₀ : L2Vector 2,
      planarL2Pullback v₀ = a ∧ Tendsto v atTop (𝓝 v₀) := by
  have hmem : ∀ᶠ n : ℕ in atTop,
      planarL2Pullback (v n) ∈ Set.range planarL2Pullback :=
    Filter.Eventually.of_forall (fun n : ℕ => ⟨v n, rfl⟩)
  have ha : a ∈ Set.range planarL2Pullback :=
    planarL2Pullback_closedRange.mem_of_tendsto h hmem
  obtain ⟨v₀, hv₀⟩ := ha
  refine ⟨v₀, hv₀, ?_⟩
  apply (planarL2Pullback_tendsto_iff v atTop v₀).mpr
  simpa only [hv₀] using h

end
end NSE_NOH

#print axioms NSE_NOH.scalarL2Pullback_closedRange
#print axioms NSE_NOH.planarL2Pullback_closedRange
#print axioms NSE_NOH.scalarL2Pullback_closure_iff
#print axioms NSE_NOH.planarL2Pullback_closure_iff
#print axioms NSE_NOH.scalarL2Pullback_uniqueFactorization
#print axioms NSE_NOH.planarL2Pullback_uniqueFactorization
#print axioms NSE_NOH.scalarL2Pullback_approximationFactorization
#print axioms NSE_NOH.planarL2Pullback_approximationFactorization
#print axioms NSE_NOH.scalarL2Pullback_tendsto_iff
#print axioms NSE_NOH.planarL2Pullback_tendsto_iff
#print axioms NSE_NOH.scalarL2Pullback_limitFactorization
#print axioms NSE_NOH.planarL2Pullback_limitFactorization
