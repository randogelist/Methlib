import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalInitialPhysicalFourier

/-! Concrete physical input and trajectory semantics for the frozen theorem.
No existence, continuation, restart, or regularity property is a datum field.
-/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB

open SingularClosure
noncomputable section

/-- Distributional solenoidality and zero mean of an actual physical L2 datum. -/
structure EnergySigmaZero (a : CriticalPhysicalL2) : Prop where
  gradient_annihilation : ∀ p : Vec → ℝ,
    ContDiff ℝ ∞ p → SpatialPeriodic p →
      physicalFieldInner (a : Field) (SingularClosure.gradient p) = 0
  mean_zero : ∀ i : Fin 3,
    physicalFieldInner (a : Field) (fun _ => unitVector i) = 0

abbrev EnergyDatum := {a : CriticalPhysicalL2 // EnergySigmaZero a}

/-- Actual weak spatial derivative representative, with no smoothness requirement. -/
abbrev WeakGradientTrajectory := ℝ → Vec → (Vec →L[ℝ] Vec)

/-- Standard physical Leray--Hopf membership, existential only in the gradient. -/
def LerayHopf (ν : ℝ) (a : CriticalPhysicalL2) (u : Velocity) : Prop :=
  ∃ G : WeakGradientTrajectory, CriticalLerayHopf ν a u G

def Shift (s : ℝ) (u : Velocity) : Velocity := fun t => u (s + t)

/-- Equality in the spatial L2 classes at every nonnegative time. -/
def SameVelocity (u v : Velocity) : Prop :=
  ∀ t : ℝ, 0 ≤ t → u t =ᵐ[volume.restrict unitCube] v t

/-- The exact frozen time bound; no unspecified small-data constant occurs. -/
def cutoff (a : CriticalPhysicalL2) (ν : ℝ) : ℝ :=
  ‖a‖ ^ 4 / (8 * Real.pi ^ 2 * ν ^ 5)

def safeCutoff (a : CriticalPhysicalL2) (ν : ℝ) : ℝ := 2 * cutoff a ν

end
end QuasiFeffermanB
