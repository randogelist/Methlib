import SingularClosure.SmoothSixProjectionAlgebra

/-!
# Orthogonality of the concrete smooth physical channels

The pairing in this module is the actual Lebesgue integral of the Euclidean
inner product on the physical unit cube. No Fourier representation premise is
used in the self-adjointness or orthogonality statements.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def physicalFieldInner (a b : Field) : ℝ :=
  ∫ x in unitCube, inner ℝ (a x) (b x)

theorem physicalFieldInner_integrable (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    IntegrableOn (fun x => inner ℝ (a x) (b x)) unitCube volume :=
  (ha.inner hb).continuousOn.integrableOn_compact isCompact_unitCube

theorem physicalFieldInner_sub_left (a b c : Field)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    physicalFieldInner (a - b) c = physicalFieldInner a c - physicalFieldInner b c := by
  unfold physicalFieldInner
  simp_rw [Pi.sub_apply, inner_sub_left]
  exact integral_sub (physicalFieldInner_integrable a c ha hc)
    (physicalFieldInner_integrable b c hb hc)

theorem physicalFieldInner_sub_right (a b c : Field)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    physicalFieldInner a (b - c) = physicalFieldInner a b - physicalFieldInner a c := by
  unfold physicalFieldInner
  simp_rw [Pi.sub_apply, inner_sub_right]
  exact integral_sub (physicalFieldInner_integrable a b ha hb)
    (physicalFieldInner_integrable a c ha hc)

theorem verticalComponentCLM_selfAdjoint (v w : Vec) :
    inner ℝ (verticalComponentCLM v) w = inner ℝ v (verticalComponentCLM w) := by
  simp [verticalComponentCLM, unitVector, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, mul_comm]

theorem verticalComponent_selfAdjoint (a b : Field) :
    physicalFieldInner (verticalComponent a) b =
      physicalFieldInner a (verticalComponent b) := by
  unfold physicalFieldInner verticalComponent
  congr 1
  funext x
  exact verticalComponentCLM_selfAdjoint (a x) (b x)

theorem baseChannelW_selfAdjoint (a b : Field)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    physicalFieldInner (baseChannelW a) b = physicalFieldInner a (baseChannelW b) := by
  change physicalFieldInner (verticalComponent (coordinateAverage 2 a)) b = _
  rw [verticalComponent_selfAdjoint]
  change (∫ x in unitCube, inner ℝ (coordinateAverage 2 a x) (verticalComponent b x)) = _
  rw [coordinateAverage_selfAdjoint 2 a (verticalComponent b) ha.continuous
    (verticalComponent_smooth hb).continuous]
  change physicalFieldInner a (coordinateAverage 2 (verticalComponent b)) = _
  rw [coordinateAverage_verticalComponent 2 b hb.continuous]
  all_goals rfl

theorem baseChannelV_selfAdjoint (a b : Field)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    physicalFieldInner (baseChannelV a) b = physicalFieldInner a (baseChannelV b) := by
  change physicalFieldInner (coordinateAverage 2 a - baseChannelW a) b =
    physicalFieldInner a (coordinateAverage 2 b - baseChannelW b)
  rw [physicalFieldInner_sub_left _ _ _ (coordinateAverage_smooth 2 a ha).continuous
      (baseChannelW_smooth ha).continuous hb.continuous,
    physicalFieldInner_sub_right _ _ _ ha.continuous
      (coordinateAverage_smooth 2 b hb).continuous (baseChannelW_smooth hb).continuous,
    baseChannelW_selfAdjoint a b ha hb]
  exact congrArg (fun r : ℝ => r - physicalFieldInner a (baseChannelW b))
    (coordinateAverage_selfAdjoint 2 a b ha.continuous hb.continuous)

theorem baseChannelR_selfAdjoint (a b : Field)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    physicalFieldInner (baseChannelR a) b = physicalFieldInner a (baseChannelR b) := by
  unfold baseChannelR
  rw [physicalFieldInner_sub_left _ _ _ ha.continuous
      (coordinateAverage_smooth 2 a ha).continuous hb.continuous,
    physicalFieldInner_sub_right _ _ _ ha.continuous hb.continuous
      (coordinateAverage_smooth 2 b hb).continuous]
  exact congrArg (fun r : ℝ => physicalFieldInner a b - r)
    (coordinateAverage_selfAdjoint 2 a b ha.continuous hb.continuous)

theorem averaged_base_selfAdjoint (Q : Field → Field)
    (hs : ∀ a : Field, ContDiff ℝ ∞ a → ContDiff ℝ ∞ (Q a))
    (hself : ∀ a b : Field, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      physicalFieldInner (Q a) b = physicalFieldInner a (Q b))
    (hc : ∀ a : Field, ContDiff ℝ ∞ a →
      Q (coordinateAverage 0 a) = coordinateAverage 0 (Q a))
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    physicalFieldInner (coordinateAverage 0 (Q a)) b =
      physicalFieldInner a (coordinateAverage 0 (Q b)) := by
  change (∫ x in unitCube, inner ℝ (coordinateAverage 0 (Q a) x) (b x)) = _
  rw [coordinateAverage_selfAdjoint 0 (Q a) b (hs a ha).continuous hb.continuous]
  change physicalFieldInner (Q a) (coordinateAverage 0 b) = _
  rw [hself a (coordinateAverage 0 b) ha (coordinateAverage_smooth 0 b hb), hc b hb]

theorem remainder_base_selfAdjoint (Q : Field → Field)
    (hs : ∀ a : Field, ContDiff ℝ ∞ a → ContDiff ℝ ∞ (Q a))
    (hself : ∀ a b : Field, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      physicalFieldInner (Q a) b = physicalFieldInner a (Q b))
    (hc : ∀ a : Field, ContDiff ℝ ∞ a →
      Q (coordinateAverage 0 a) = coordinateAverage 0 (Q a))
    (a b : Field) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    physicalFieldInner (Q a - coordinateAverage 0 (Q a)) b =
      physicalFieldInner a (Q b - coordinateAverage 0 (Q b)) := by
  rw [physicalFieldInner_sub_left _ _ _ (hs a ha).continuous
      (coordinateAverage_smooth 0 (Q a) (hs a ha)).continuous hb.continuous,
    physicalFieldInner_sub_right _ _ _ ha.continuous (hs b hb).continuous
      (coordinateAverage_smooth 0 (Q b) (hs b hb)).continuous,
    hself a b ha hb, averaged_base_selfAdjoint Q hs hself hc a b ha hb]

/-- Each literal smooth physical channel is self-adjoint for the cube pairing. -/
theorem smoothSixChannel_selfAdjoint (A : Fin 6) (a b : Field)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    (∫ x in unitCube, inner ℝ (smoothSixChannel A a x) (b x)) =
      ∫ x in unitCube, inner ℝ (a x) (smoothSixChannel A b x) := by
  have hv := averaged_base_selfAdjoint baseChannelV (fun _ h => baseChannelV_smooth h)
    baseChannelV_selfAdjoint (fun u hu => baseChannelV_coordinateAverage 0 u hu.continuous)
    a b ha hb
  have hv' := remainder_base_selfAdjoint baseChannelV (fun _ h => baseChannelV_smooth h)
    baseChannelV_selfAdjoint (fun u hu => baseChannelV_coordinateAverage 0 u hu.continuous)
    a b ha hb
  have hw := averaged_base_selfAdjoint baseChannelW (fun _ h => baseChannelW_smooth h)
    baseChannelW_selfAdjoint (fun u hu => baseChannelW_coordinateAverage 0 u hu.continuous)
    a b ha hb
  have hw' := remainder_base_selfAdjoint baseChannelW (fun _ h => baseChannelW_smooth h)
    baseChannelW_selfAdjoint (fun u hu => baseChannelW_coordinateAverage 0 u hu.continuous)
    a b ha hb
  have hr := averaged_base_selfAdjoint baseChannelR (fun _ h => baseChannelR_smooth h)
    baseChannelR_selfAdjoint (fun u hu => baseChannelR_coordinateAverage 0 u hu.continuous)
    a b ha hb
  have hr' := remainder_base_selfAdjoint baseChannelR (fun _ h => baseChannelR_smooth h)
    baseChannelR_selfAdjoint (fun u hu => baseChannelR_coordinateAverage 0 u hu.continuous)
    a b ha hb
  fin_cases A
  · exact hv
  · exact hv'
  · exact hw
  · exact hw'
  · exact hr
  · exact hr'

/-- Distinct smooth physical channels are orthogonal under the actual integral. -/
theorem smoothSixChannel_orthogonal (A B : Fin 6) (hAB : A ≠ B) (a b : Field)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    (∫ x in unitCube, inner ℝ (smoothSixChannel A a x) (smoothSixChannel B b x)) = 0 := by
  rw [smoothSixChannel_selfAdjoint A a (smoothSixChannel B b) ha
    (smoothSixChannel_smooth B b hb), smoothSixChannel_comp A B b hb.continuous, if_neg hAB]
  simp

end

end SingularClosure
