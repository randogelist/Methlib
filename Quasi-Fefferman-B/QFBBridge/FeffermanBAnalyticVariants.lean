import Mathlib.Analysis.Analytic.Basic
import QFBBridge.FeffermanBClosure

/-!
Analytic-output variants of the classical periodic Fefferman--B statement.

All four statements quantify over the same smooth divergence-free mean-zero
initial-data class.  The variants strengthen only the positive-time output.
The forward implications are isolated behind one named analytic-upgrade
premise; the converse implications are exact forgetful projections.
-/

set_option autoImplicit false
set_option Elab.async true

open Set

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- Spatial analyticity of the velocity at every strictly positive time. -/
def PositiveSpaceAnalytic (u : Velocity) : Prop :=
  ∀ t : ℝ, 0 < t → AnalyticOnNhd ℝ (u t) (Set.univ : Set Vec)

/-- Time analyticity of the velocity at every spatial point on `(0,∞)`. -/
def PositiveTimeAnalytic (u : Velocity) : Prop :=
  ∀ x : Vec, AnalyticOnNhd ℝ (fun t : ℝ => u t x) (Ioi (0 : ℝ))

/-- Joint positive-time space-time analyticity of the velocity. -/
def PositiveSpaceTimeAnalytic (u : Velocity) : Prop :=
  AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2)
    (Ioi (0 : ℝ) ×ˢ (Set.univ : Set Vec))

/-- Fefferman--B at fixed viscosity with a spatially analytic positive-time
velocity output. -/
def FeffermanBSpaceOmegaAt (ν : ℝ) : Prop :=
  ∀ a : CriticalPhysicalL2, SmoothInitialDatum a →
    Nonempty {S : GlobalClassicalSolution ν a //
      PositiveSpaceAnalytic S.velocity}

/-- Fefferman--B at fixed viscosity with a time-analytic positive-time
velocity output. -/
def FeffermanBTimeOmegaAt (ν : ℝ) : Prop :=
  ∀ a : CriticalPhysicalL2, SmoothInitialDatum a →
    Nonempty {S : GlobalClassicalSolution ν a //
      PositiveTimeAnalytic S.velocity}

/-- Fefferman--B at fixed viscosity with a jointly space-time analytic
positive-time velocity output. -/
def FeffermanBSpaceTimeOmegaAt (ν : ℝ) : Prop :=
  ∀ a : CriticalPhysicalL2, SmoothInitialDatum a →
    Nonempty {S : GlobalClassicalSolution ν a //
      PositiveSpaceTimeAnalytic S.velocity}

def FeffermanBSpaceOmegaStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → FeffermanBSpaceOmegaAt ν

def FeffermanBTimeOmegaStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → FeffermanBTimeOmegaAt ν

def FeffermanBSpaceTimeOmegaStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → FeffermanBSpaceTimeOmegaAt ν

/-- Requested short names.  The suffix `w` denotes the analytic `ω` output. -/
abbrev FB_space_w : Prop := FeffermanBSpaceOmegaStatement
abbrev FB_time_w : Prop := FeffermanBTimeOmegaStatement
abbrev FB_spacetime_w : Prop := FeffermanBSpaceTimeOmegaStatement

/-- The single unresolved analytic regularity endpoint for the first assembly:
every global classical solution has all three positive-time analytic outputs.
It is an explicit theorem premise, not a Lean axiom. -/
def FeffermanBAnalyticUpgradeStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : CriticalPhysicalL2), SmoothInitialDatum a →
      ∀ S : GlobalClassicalSolution ν a,
        PositiveSpaceAnalytic S.velocity ∧
        PositiveTimeAnalytic S.velocity ∧
        PositiveSpaceTimeAnalytic S.velocity

/-- Forget spatial analyticity and retain the classical solution. -/
theorem FEFFERMAN_B_SPACE_OMEGA_TO_FB
    (h : FeffermanBSpaceOmegaStatement) : FeffermanBStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := h ν hν a ha
  exact ⟨S.1⟩

/-- Forget time analyticity and retain the classical solution. -/
theorem FEFFERMAN_B_TIME_OMEGA_TO_FB
    (h : FeffermanBTimeOmegaStatement) : FeffermanBStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := h ν hν a ha
  exact ⟨S.1⟩

/-- Forget joint space-time analyticity and retain the classical solution. -/
theorem FEFFERMAN_B_SPACETIME_OMEGA_TO_FB
    (h : FeffermanBSpaceTimeOmegaStatement) : FeffermanBStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := h ν hν a ha
  exact ⟨S.1⟩

/-- Upgrade a classical Fefferman--B witness to the spatially analytic-output
statement. -/
theorem FEFFERMAN_B_TO_SPACE_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement)
    (hFB : FeffermanBStatement) : FeffermanBSpaceOmegaStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := hFB ν hν a ha
  exact ⟨⟨S, (hUpgrade ν hν a ha S).1⟩⟩

/-- Upgrade a classical Fefferman--B witness to the time-analytic-output
statement. -/
theorem FEFFERMAN_B_TO_TIME_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement)
    (hFB : FeffermanBStatement) : FeffermanBTimeOmegaStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := hFB ν hν a ha
  exact ⟨⟨S, (hUpgrade ν hν a ha S).2.1⟩⟩

/-- Upgrade a classical Fefferman--B witness to the jointly analytic-output
statement. -/
theorem FEFFERMAN_B_TO_SPACETIME_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement)
    (hFB : FeffermanBStatement) : FeffermanBSpaceTimeOmegaStatement := by
  intro ν hν a ha
  obtain ⟨S⟩ := hFB ν hν a ha
  exact ⟨⟨S, (hUpgrade ν hν a ha S).2.2⟩⟩

/-- Classical Fefferman--B is equivalent to its positive-space-analytic output
form, conditional only on the named analytic-upgrade endpoint. -/
theorem FEFFERMAN_B_IFF_SPACE_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement) :
    FeffermanBStatement ↔ FeffermanBSpaceOmegaStatement :=
  ⟨FEFFERMAN_B_TO_SPACE_OMEGA hUpgrade,
    FEFFERMAN_B_SPACE_OMEGA_TO_FB⟩

/-- Classical Fefferman--B is equivalent to its positive-time-analytic output
form, conditional only on the named analytic-upgrade endpoint. -/
theorem FEFFERMAN_B_IFF_TIME_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement) :
    FeffermanBStatement ↔ FeffermanBTimeOmegaStatement :=
  ⟨FEFFERMAN_B_TO_TIME_OMEGA hUpgrade,
    FEFFERMAN_B_TIME_OMEGA_TO_FB⟩

/-- Classical Fefferman--B is equivalent to its positive-space-time-analytic
output form, conditional only on the named analytic-upgrade endpoint. -/
theorem FEFFERMAN_B_IFF_SPACETIME_OMEGA
    (hUpgrade : FeffermanBAnalyticUpgradeStatement) :
    FeffermanBStatement ↔ FeffermanBSpaceTimeOmegaStatement :=
  ⟨FEFFERMAN_B_TO_SPACETIME_OMEGA hUpgrade,
    FEFFERMAN_B_SPACETIME_OMEGA_TO_FB⟩

/-- Exact three-equivalence assembly requested for the uniqueness reattempt. -/
theorem FEFFERMAN_B_ANALYTIC_EQUIVALENCE_TRIPLE
    (hUpgrade : FeffermanBAnalyticUpgradeStatement) :
    (FeffermanBStatement ↔ FB_space_w) ∧
    (FeffermanBStatement ↔ FB_time_w) ∧
    (FeffermanBStatement ↔ FB_spacetime_w) := by
  exact ⟨FEFFERMAN_B_IFF_SPACE_OMEGA hUpgrade,
    FEFFERMAN_B_IFF_TIME_OMEGA hUpgrade,
    FEFFERMAN_B_IFF_SPACETIME_OMEGA hUpgrade⟩

end
end QuasiFeffermanB
