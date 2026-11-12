import QuasiFeffermanB.Semantics

/-! Exact concrete root contract. This file defines the target proposition;
it does not postulate or prove its analytic endpoints. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff ENNReal Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def tailSpacetime (δ : ℝ) : Set (ℝ × Vec) := {z | δ ≤ z.1}

/-- Actual smooth NSE equations on the closed regular tail. -/
structure ClassicalTail (ν δ : ℝ) (v : Velocity) (p : Pressure) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2) (tailSpacetime δ)
  pressure_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (tailSpacetime δ)
  velocity_periodic : ∀ t : ℝ, δ ≤ t → SpatialPeriodic (v t)
  pressure_periodic : ∀ t : ℝ, δ ≤ t → SpatialPeriodic (p t)
  divergence_free : ∀ t : ℝ, δ ≤ t → ∀ x : Vec, divergence (v t) x = 0
  equation : ∀ t : ℝ, δ ≤ t → ∀ x : Vec,
    timeDerivative v t x + convection (v t) x + gradient (p t) x =
      ν • laplacian (v t) x
  velocity_mean_zero : ∀ t : ℝ, δ ≤ t → MeanZero (v t)
  pressure_mean_zero : ∀ t : ℝ, δ ≤ t → PressureMeanZero (p t)

/-- Spatial null-set modifications do not create different regular tails. -/
def HasSmoothTail (ν : ℝ) (u : Velocity) (δ : ℝ) : Prop :=
  ∃ (v : Velocity) (p : Pressure), ClassicalTail ν δ v p ∧
    ∀ t : ℝ, δ ≤ t → u t =ᵐ[volume.restrict unitCube] v t

def TailEnergyEquality (ν : ℝ) (u : Velocity)
    (G : WeakGradientTrajectory) (δ : ℝ) : Prop :=
  ∀ t : ℝ, δ ≤ t →
    physicalEnergy (u t) +
      2 * ν * (∫ r in δ..t, criticalGradientEnergy (G r)) = physicalEnergy (u δ)

/-- Membership of the translated original path and uniqueness of its future. -/
def UniqueFuture (ν : ℝ) (u : Velocity)
    (G : WeakGradientTrajectory) (δ : ℝ) : Prop :=
  CriticalLerayHopf ν (criticalL2Representative (u δ)) (Shift δ u)
      (fun t => G (δ + t)) ∧
    ∀ (v : Velocity) (H : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative (u δ)) v H →
        SameVelocity v (Shift δ u)

/-- Frozen universal statement: original datum, every LH path, exact cutoff,
actual physical equations, energy equality, and uniqueness from each trace. -/
def QuasiFeffermanBStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : CriticalPhysicalL2), EnergySigmaZero a →
    (∃ (u : Velocity) (G : WeakGradientTrajectory), CriticalLerayHopf ν a u G) ∧
    ∀ (u : Velocity) (G : WeakGradientTrajectory), CriticalLerayHopf ν a u G →
      HasSmoothTail ν u (safeCutoff a ν) ∧
      ∀ (δ : ℝ), cutoff a ν < δ →
        HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ

end
end QuasiFeffermanB
