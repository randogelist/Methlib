import NSE_NOH_TorusMass
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# NSE_NOH FIX16: L² isometric pullback and strong rough-trace preservation

Previous FIX15 proved that the physical projection from the normalized
three-dimensional torus onto the two-dimensional torus is measure preserving.
This module applies the ACTUAL Mathlib Lp.compMeasurePreserving isometry to
arbitrary measurable L² classes; no H¹/² smallness or smooth trace is assumed.

These are forward embeddings from two dimensions to three. They do not show
that every distributionally x1-invariant 3D L² class admits such a factorization.
They do not construct a 2D NSE or passive-scalar evolution.

Prepared for the user's external native Windows Lean 4.33.0 compiler;
NO_LOCAL_LEAN, and external theorem-level axiom audit REQUIRED.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory
open scoped ENNReal

namespace NSE_NOH
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-! Pullback of an arbitrary two-dimensional L² scalar class. -/
def scalarL2Pullback :
    L2Scalar2 →ₗᵢ[ℝ]
      Lp ℝ (2 : ℝ≥0∞) (volume : Measure (Torus 3)) :=
  Lp.compMeasurePreservingₗᵢ ℝ torusProjection2
    torusProjection2_measurePreserving

/-! Pullback of an arbitrary two-dimensional L² planar vector class.
The Lp Banach norm here follows the existing `Vector 2` norm. The
physical Euclidean kinetic energy remains the separately defined mass. -/
def planarL2Pullback :
    L2Vector 2 →ₗᵢ[ℝ]
      Lp (Vector 2) (2 : ℝ≥0∞) (volume : Measure (Torus 3)) :=
  Lp.compMeasurePreservingₗᵢ ℝ torusProjection2
    torusProjection2_measurePreserving

/-! The pullbacks agree with the genuine coordinate composition almost everywhere. -/
theorem scalarL2Pullback_ae (w : L2Scalar2) :
    (scalarL2Pullback w : Torus 3 → ℝ) =ᵐ[(volume : Measure (Torus 3))]
      (fun x => w (torusProjection2 x)) := by
  exact Lp.coeFn_compMeasurePreserving w torusProjection2_measurePreserving

theorem planarL2Pullback_ae (v : L2Vector 2) :
    (planarL2Pullback v : Torus 3 → Vector 2) =ᵐ[(volume : Measure (Torus 3))]
      (fun x => v (torusProjection2 x)) := by
  exact Lp.coeFn_compMeasurePreserving v torusProjection2_measurePreserving

/-! No loss or gain in the L² norm on lifting. -/
theorem scalarL2Pullback_norm (w : L2Scalar2) :
    ‖scalarL2Pullback w‖ = ‖w‖ := by
  exact scalarL2Pullback.norm_map w

theorem planarL2Pullback_norm (v : L2Vector 2) :
    ‖planarL2Pullback v‖ = ‖v‖ := by
  exact planarL2Pullback.norm_map v

/-! Exact preservation of L² distances and uniqueness of planar preimages. -/
theorem scalarL2Pullback_dist (w z : L2Scalar2) :
    dist (scalarL2Pullback w) (scalarL2Pullback z) = dist w z := by
  exact scalarL2Pullback.isometry.dist_eq w z

theorem planarL2Pullback_dist (v z : L2Vector 2) :
    dist (planarL2Pullback v) (planarL2Pullback z) = dist v z := by
  exact planarL2Pullback.isometry.dist_eq v z

theorem scalarL2Pullback_injective : Function.Injective scalarL2Pullback :=
  scalarL2Pullback.injective

theorem planarL2Pullback_injective : Function.Injective planarL2Pullback :=
  planarL2Pullback.injective

/-! A continuous L² trajectory with arbitrary rough initial trace
remains continuous with the same prescribed trace after lifting. -/
theorem scalarL2Pullback_strongTrace
    (w : NNReal → L2Scalar2) (w₀ : L2Scalar2)
    (hw : Continuous w) (hw₀ : w 0 = w₀) :
    Continuous (fun t : NNReal => scalarL2Pullback (w t)) ∧
      scalarL2Pullback (w 0) = scalarL2Pullback w₀ := by
  exact ⟨scalarL2Pullback.continuous.comp hw,
    congrArg scalarL2Pullback hw₀⟩

theorem planarL2Pullback_strongTrace
    (v : NNReal → L2Vector 2) (v₀ : L2Vector 2)
    (hv : Continuous v) (hv₀ : v 0 = v₀) :
    Continuous (fun t : NNReal => planarL2Pullback (v t)) ∧
      planarL2Pullback (v 0) = planarL2Pullback v₀ := by
  exact ⟨planarL2Pullback.continuous.comp hv,
    congrArg planarL2Pullback hv₀⟩

/-! The physical scalar kinetic mass is preserved even for rough L²
classes. No pointwise initial regularity is required. -/
theorem scalarL2Pullback_mass (w : L2Scalar2) :
    (∫ x : Torus 3, ((scalarL2Pullback w) x) ^ (2 : ℕ)) =
      scalarMass w := by
  calc
    (∫ x : Torus 3, ((scalarL2Pullback w) x) ^ (2 : ℕ)) =
        (∫ x : Torus 3, (w (torusProjection2 x)) ^ (2 : ℕ)) := by
      apply integral_congr_ae
      filter_upwards [scalarL2Pullback_ae w] with x hx
      rw [hx]
    _ = scalarMass w := by
      exact integral_torusProjection2
        (fun y : Torus 2 => (w y) ^ (2 : ℕ))
        ((Lp.aestronglyMeasurable w).pow 2)

end
end NSE_NOH

#print axioms NSE_NOH.scalarL2Pullback_ae
#print axioms NSE_NOH.planarL2Pullback_ae
#print axioms NSE_NOH.scalarL2Pullback_norm
#print axioms NSE_NOH.planarL2Pullback_norm
#print axioms NSE_NOH.scalarL2Pullback_dist
#print axioms NSE_NOH.planarL2Pullback_dist
#print axioms NSE_NOH.scalarL2Pullback_injective
#print axioms NSE_NOH.planarL2Pullback_injective
#print axioms NSE_NOH.scalarL2Pullback_strongTrace
#print axioms NSE_NOH.planarL2Pullback_strongTrace
#print axioms NSE_NOH.scalarL2Pullback_mass
