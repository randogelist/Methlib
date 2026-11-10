import NSE_NOH_Energy
import Mathlib.MeasureTheory.Integral.Pi

/-!
# NSE_NOH FIX15: Normalized torus projection and actual integrated kinetic mass

This module promotes the pointwise FIX13 mass-density identity to an
integral identity on the *actual normalized* unit torus, not an abstract
postulated integral. The first-coordinate marginal is a probability
measure. It does NOT construct a 2D NSE solution, a passive scalar, or
an L² trace, and does NOT yet transfer real-cube Dirichlet integrals.

The proofs below are candidates for the user's external Windows Lean
4.33.0 compiler; no local Lean execution is performed.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory

namespace NSE_NOH
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Forgetting the first spatial coordinate preserves normalized Haar
measure on the unit torus. This is an actual measure-theoretic theorem,
not an `AnalyticPorts` assumption. -/
theorem torusProjection2_measurePreserving :
    MeasurePreserving torusProjection2
      (volume : Measure (Torus 3))
      (volume : Measure (Torus 2)) := by
  let e : Torus 3 ≃ᵐ UnitAddCircle × Torus 2 :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => UnitAddCircle) 0
  -- The piFinSuccAbove API targets `volume` on the product type.
  -- Convert that actual product-space volume into `volume.prod volume`;
  -- the two measures are propositionally equal, not elaborator-identical.
  have he0 : MeasurePreserving e
      (volume : Measure (Torus 3))
      (volume : Measure (UnitAddCircle × Torus 2)) := by
    change MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin 3 => UnitAddCircle) (0 : Fin 3))
      (volume : Measure (Torus 3))
      (volume : Measure (UnitAddCircle × Torus 2))
    exact MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => UnitAddCircle) (0 : Fin 3)
  have he : MeasurePreserving e
      (volume : Measure (Torus 3))
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Torus 2))) := by
    simpa only [Measure.volume_eq_prod] using he0
  have hs : MeasurePreserving Prod.snd
      ((volume : Measure UnitAddCircle).prod (volume : Measure (Torus 2)))
      (volume : Measure (Torus 2)) :=
    MeasureTheory.measurePreserving_snd
  have hfun : (Prod.snd ∘ e : Torus 3 → Torus 2) = torusProjection2 := by
    funext x
    ext i
    first
    | rfl
    | simpa only [Function.comp_apply, e, torusProjection2,
        MeasurableEquiv.piFinSuccAbove_apply, Fin.zero_succAbove]
  simpa only [hfun] using hs.comp he

/-- Every a.e. strongly measurable scalar on the two-torus has the same
Bochner integral after pullback to the three-torus. Integrability is not
asserted if the integrand is not integrable. -/
theorem integral_torusProjection2 (f : Torus 2 → ℝ)
    (hf : AEStronglyMeasurable f (volume : Measure (Torus 2))) :
    (∫ x : Torus 3, f (torusProjection2 x)) =
      ∫ y : Torus 2, f y := by
  have hp := torusProjection2_measurePreserving
  have hm : AEStronglyMeasurable f
      (Measure.map torusProjection2 (volume : Measure (Torus 3))) := by
    simpa only [hp.map_eq] using hf
  calc
    (∫ x : Torus 3, f (torusProjection2 x)) =
        ∫ y : Torus 2, f y
          ∂(Measure.map torusProjection2 (volume : Measure (Torus 3))) := by
      exact (MeasureTheory.integral_map hp.measurable.aemeasurable hm).symm
    _ = ∫ y : Torus 2, f y := by rw [hp.map_eq]

/-- Three-component velocity induced by a scalar and a planar vector
on the actual compact unit torus. -/
def torusLiftedVector (w : Torus 2 → ℝ)
    (v : Torus 2 → Vector 2) : Torus 3 → Vector 3 :=
  fun x => ![w (torusProjection2 x),
             v (torusProjection2 x) 0,
             v (torusProjection2 x) 1]

/-- Pointwise kinetic mass identity for actual torus fields. -/
theorem squareMassDensity_torusLiftedVector
    (w : Torus 2 → ℝ) (v : Torus 2 → Vector 2) (x : Torus 3) :
    squareMassDensity 3 (torusLiftedVector w v x) =
      (w (torusProjection2 x)) ^ (2 : ℕ) +
        squareMassDensity 2 (v (torusProjection2 x)) := by
  -- `ring` cannot simplify `![a,b,c] i` unless the component
  -- projections have first been exposed by definitional reduction.
  simp only [squareMassDensity, Fin.sum_univ_three, Fin.sum_univ_two]
  change
      (w (torusProjection2 x)) ^ (2 : ℕ) +
        (v (torusProjection2 x) 0) ^ (2 : ℕ) +
          (v (torusProjection2 x) 1) ^ (2 : ℕ) =
      (w (torusProjection2 x)) ^ (2 : ℕ) +
        ((v (torusProjection2 x) 0) ^ (2 : ℕ) +
          (v (torusProjection2 x) 1) ^ (2 : ℕ))
  ring

/-- Integrated physical torus kinetic mass, with no hidden analytic
existence assumption. The supplied L¹ hypotheses are exactly those
needed to justify linearity of the Bochner integral. -/
theorem integral_squareMassDensity_torusLiftedVector
    (w : Torus 2 → ℝ) (v : Torus 2 → Vector 2)
    (hw : Integrable (fun y : Torus 2 => (w y) ^ (2 : ℕ)))
    (hv : Integrable (fun y : Torus 2 => squareMassDensity 2 (v y))) :
    (∫ x : Torus 3, squareMassDensity 3 (torusLiftedVector w v x)) =
      (∫ y : Torus 2, (w y) ^ (2 : ℕ)) +
        (∫ y : Torus 2, squareMassDensity 2 (v y)) := by
  have hp := torusProjection2_measurePreserving
  have hw3 : Integrable
      (fun x : Torus 3 => (w (torusProjection2 x)) ^ (2 : ℕ)) := by
    simpa only [Function.comp_def] using
      hp.integrable_comp_of_integrable hw
  have hv3 : Integrable
      (fun x : Torus 3 => squareMassDensity 2 (v (torusProjection2 x))) := by
    simpa only [Function.comp_def] using
      hp.integrable_comp_of_integrable hv
  calc
    (∫ x : Torus 3, squareMassDensity 3 (torusLiftedVector w v x)) =
        ∫ x : Torus 3,
          ((w (torusProjection2 x)) ^ (2 : ℕ) +
            squareMassDensity 2 (v (torusProjection2 x))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        squareMassDensity_torusLiftedVector w v x)
    _ = (∫ x : Torus 3, (w (torusProjection2 x)) ^ (2 : ℕ)) +
        (∫ x : Torus 3, squareMassDensity 2 (v (torusProjection2 x))) := by
      exact integral_add hw3 hv3
    _ = (∫ y : Torus 2, (w y) ^ (2 : ℕ)) +
          (∫ y : Torus 2, squareMassDensity 2 (v y)) := by
      rw [integral_torusProjection2 _ hw.aestronglyMeasurable,
          integral_torusProjection2 _ hv.aestronglyMeasurable]

end
end NSE_NOH

#print axioms NSE_NOH.torusProjection2_measurePreserving
#print axioms NSE_NOH.integral_torusProjection2
#print axioms NSE_NOH.squareMassDensity_torusLiftedVector
#print axioms NSE_NOH.integral_squareMassDensity_torusLiftedVector
