import SingularClosure.SmoothSixChannels

/-!
# Projection algebra of the six physical channels

All equalities act on the literal Euclidean-space lifts. The only analytic
input for the algebra is continuity, ensuring linearity of the integrals.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem coordinateAverage_sub (j : Fin 3) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    coordinateAverage j (a - b) = coordinateAverage j a - coordinateAverage j b := by
  funext x
  exact integral_sub (coordinateAverage_slice_integrable j a ha x)
    (coordinateAverage_slice_integrable j b hb x)

theorem coordinateAverage_neg (j : Fin 3) (a : Field) :
    coordinateAverage j (-a) = -coordinateAverage j a := by
  funext x
  exact integral_neg (fun s : ℝ => a (resetCoordinate j s x))

theorem verticalComponent_continuous (a : Field) (ha : Continuous a) :
    Continuous (verticalComponent a) := verticalComponentCLM.continuous.comp ha

theorem verticalComponent_zero : verticalComponent (0 : Field) = 0 := by
  funext x
  exact map_zero verticalComponentCLM

theorem verticalComponent_add (a b : Field) :
    verticalComponent (a + b) = verticalComponent a + verticalComponent b := by
  funext x
  exact map_add verticalComponentCLM (a x) (b x)

theorem verticalComponent_sub (a b : Field) :
    verticalComponent (a - b) = verticalComponent a - verticalComponent b := by
  funext x
  exact map_sub verticalComponentCLM (a x) (b x)

theorem verticalComponent_neg (a : Field) :
    verticalComponent (-a) = -verticalComponent a := by
  funext x
  exact map_neg verticalComponentCLM (a x)

theorem verticalComponent_smul (r : ℝ) (a : Field) :
    verticalComponent (r • a) = r • verticalComponent a := by
  funext x
  exact map_smul verticalComponentCLM r (a x)

theorem verticalComponent_idempotent (a : Field) :
    verticalComponent (verticalComponent a) = verticalComponent a := by
  funext x
  simp [verticalComponent, verticalComponentCLM, unitVector]

theorem coordinateAverage_verticalComponent (j : Fin 3) (a : Field)
    (ha : Continuous a) :
    coordinateAverage j (verticalComponent a) =
      verticalComponent (coordinateAverage j a) := by
  funext x
  exact verticalComponentCLM.integral_comp_comm
    (coordinateAverage_slice_integrable j a ha x)

/-- The fixed third-coordinate average commutes with the first-coordinate average. -/
theorem coordinateAverage_two_zero (a : Field) (ha : Continuous a) :
    coordinateAverage 2 (coordinateAverage 0 a) =
      coordinateAverage 0 (coordinateAverage 2 a) :=
  coordinateAverage_commute 2 0 a ha

theorem baseChannelV_coordinateAverage (j : Fin 3) (a : Field)
    (ha : Continuous a) :
    baseChannelV (coordinateAverage j a) = coordinateAverage j (baseChannelV a) := by
  unfold baseChannelV
  rw [coordinateAverage_sub j _ _ (coordinateAverage_continuous 2 a ha)
    (verticalComponent_continuous _ (coordinateAverage_continuous 2 a ha)),
    coordinateAverage_verticalComponent j _ (coordinateAverage_continuous 2 a ha),
    coordinateAverage_commute 2 j a ha]

theorem baseChannelW_coordinateAverage (j : Fin 3) (a : Field)
    (ha : Continuous a) :
    baseChannelW (coordinateAverage j a) = coordinateAverage j (baseChannelW a) := by
  unfold baseChannelW
  rw [coordinateAverage_verticalComponent j _ (coordinateAverage_continuous 2 a ha),
    coordinateAverage_commute 2 j a ha]

theorem baseChannelR_coordinateAverage (j : Fin 3) (a : Field)
    (ha : Continuous a) :
    baseChannelR (coordinateAverage j a) = coordinateAverage j (baseChannelR a) := by
  unfold baseChannelR
  rw [coordinateAverage_sub j _ _ ha (coordinateAverage_continuous 2 a ha),
    coordinateAverage_commute 2 j a ha]

private theorem channel_continuous_sub (a b : Field)
    (ha : Continuous a) (hb : Continuous b) : Continuous (a - b) := by
  change Continuous (fun x => a x - b x)
  exact ha.sub hb

private theorem channel_continuous_add (a b : Field)
    (ha : Continuous a) (hb : Continuous b) : Continuous (a + b) := by
  change Continuous (fun x => a x + b x)
  exact ha.add hb

private theorem channel_continuous_neg (a : Field)
    (ha : Continuous a) : Continuous (-a) := by
  change Continuous (fun x => -a x)
  exact ha.neg

private theorem channel_continuous_zero : Continuous (0 : Field) := continuous_const

theorem smoothSixChannel_continuous (A : Fin 6) (a : Field) (ha : Continuous a) :
    Continuous (smoothSixChannel A a) := by
  have hp := coordinateAverage_continuous 2 a ha
  have hw := verticalComponent_continuous _ hp
  have hv := channel_continuous_sub _ _ hp hw
  have hr := channel_continuous_sub _ _ ha hp
  fin_cases A
  · exact coordinateAverage_continuous 0 _ hv
  · exact channel_continuous_sub _ _ hv (coordinateAverage_continuous 0 _ hv)
  · exact coordinateAverage_continuous 0 _ hw
  · exact channel_continuous_sub _ _ hw (coordinateAverage_continuous 0 _ hw)
  · exact coordinateAverage_continuous 0 _ hr
  · exact channel_continuous_sub _ _ hr (coordinateAverage_continuous 0 _ hr)

theorem smoothSixChannel_zero (A : Fin 6) : smoothSixChannel A (0 : Field) = 0 := by
  fin_cases A <;>
    simp [smoothSixChannel, baseChannelV, baseChannelW, baseChannelR,
      coordinateAverage_zero, verticalComponent_zero]

theorem smoothSixChannel_add (A : Fin 6) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    smoothSixChannel A (a + b) = smoothSixChannel A a + smoothSixChannel A b := by
  fin_cases A <;>
    simp (disch := solve_by_elim (maxDepth := 32)
      [coordinateAverage_continuous, verticalComponent_continuous,
        channel_continuous_sub, channel_continuous_add, channel_continuous_neg,
        channel_continuous_zero])
      [smoothSixChannel, baseChannelV, baseChannelW, baseChannelR,
        coordinateAverage_sub, coordinateAverage_add, verticalComponent_sub,
        verticalComponent_add] <;> abel

theorem smoothSixChannel_smul (A : Fin 6) (r : ℝ) (a : Field) :
    smoothSixChannel A (r • a) = r • smoothSixChannel A a := by
  fin_cases A <;>
    simp [smoothSixChannel, baseChannelV, baseChannelW, baseChannelR,
      coordinateAverage_smul, verticalComponent_smul, ← smul_sub]

set_option maxHeartbeats 1000000 in
/-- Orthogonal-mask composition, obtained solely from actual average algebra. -/
theorem smoothSixChannel_comp (A B : Fin 6) (a : Field) (ha : Continuous a) :
    smoothSixChannel A (smoothSixChannel B a) =
      if A = B then smoothSixChannel A a else 0 := by
  fin_cases A <;> fin_cases B <;>
    simp (disch := solve_by_elim (maxDepth := 32)
      [coordinateAverage_continuous, verticalComponent_continuous,
        channel_continuous_sub, channel_continuous_add, channel_continuous_neg,
        channel_continuous_zero])
      [smoothSixChannel, baseChannelV, baseChannelW, baseChannelR,
        coordinateAverage_sub, coordinateAverage_add, coordinateAverage_neg,
        coordinateAverage_zero, coordinateAverage_verticalComponent,
        coordinateAverage_two_zero, coordinateAverage_idempotent,
        verticalComponent_sub, verticalComponent_add, verticalComponent_neg,
        verticalComponent_idempotent, verticalComponent_zero] <;> abel

theorem smoothSixChannel_idempotent (A : Fin 6) (a : Field) (ha : Continuous a) :
    smoothSixChannel A (smoothSixChannel A a) = smoothSixChannel A a := by
  simpa using smoothSixChannel_comp A A a ha

theorem smoothSixChannel_disjoint (A B : Fin 6) (hAB : A ≠ B)
    (a : Field) (ha : Continuous a) :
    smoothSixChannel A (smoothSixChannel B a) = 0 := by
  simpa [hAB] using smoothSixChannel_comp A B a ha

end

end SingularClosure
