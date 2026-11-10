import S_DIR_L2_SCHUR_KERNEL

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace SDirL2

/-!
# Deterministic conditional assembly for frozen S_DIR_L2_GLOBAL_REGULARITY

The global root is an exact proposition declared by the unchanged
`S_DIR_L2_GLOBAL_REGULARITY.lean`. This file exposes each remaining
semantic/analytic edge independently and composes them without `sorry`,
custom axioms, or manufactured analytic certificates.

A proof of this theorem is conditional on hP1 hP2 hP3. It is NOT an
unconditional proof that a genuine physical-space NSE heat solution
has the stated properties. That stronger theorem requires actual
concrete P1/P2/P3 implementations and a faithful PhysicalSemantics.
-/

/-- P1: Physical torus heat synthesis, joint smoothing, energy and trace. -/
def S_DIR_L2_P1_PHYSICAL_SYNTHESIS (P : PhysicalSemantics) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ u : L2DirectionalDatum,
    ∃ v : TimeSpaceVelocity,
      P.IsHeatOrbit ν u v ∧
      P.IsLerayHopf ν u v ∧
      P.StrongL2Trace ν u v ∧
      P.JointSmoothInterior ν u v ∧
      P.EnergyEquality ν u v

/-- P2: Uniform rank-two Schur + global critical L²_t L∞_x control. -/
def S_DIR_L2_P2_SERRIN (P : PhysicalSemantics) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u : L2DirectionalDatum)
    (v : TimeSpaceVelocity),
    P.IsHeatOrbit ν u v →
    P.GlobalSerrin2Infinity ν u v

/-- P3: Weak–strong uniqueness among every physical 3D Leray–Hopf solution. -/
def S_DIR_L2_P3_LERAY_HOPF_UNIQUENESS (P : PhysicalSemantics) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u : L2DirectionalDatum)
    (v : TimeSpaceVelocity),
    P.IsLerayHopf ν u v →
    P.GlobalSerrin2Infinity ν u v →
    P.UniqueAmongAllLerayHopf ν u v

/--
Exact conditional proof spine; no P1/P2/P3 field is constructed here.
The known unconditional Fourier-M7 statement is used through the
already compiled base theorem.
-/
theorem S_DIR_L2_GLOBAL_REGULARITY_PROOF_SPINE
    (P : PhysicalSemantics)
    (hP1 : S_DIR_L2_P1_PHYSICAL_SYNTHESIS P)
    (hP2 : S_DIR_L2_P2_SERRIN P)
    (hP3 : S_DIR_L2_P3_LERAY_HOPF_UNIQUENESS P) :
    S_DIR_L2_GLOBAL_REGULARITY P := by
  exact S_DIR_L2_GLOBAL_REGULARITY_of_certificates P
    { physicalHeatSynthesis := hP1
      uniformRankTwoSchurAndSerrin := hP2
      relativeEnergyWeakStrongUniqueness := hP3 }

end SDirL2
