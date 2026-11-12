import QuasiFeffermanB.RootAssembly
import QuasiFeffermanB.CaloricNumericalAdmission

/-! Actual all-LH conclusions with numerical admission discharged.
Existence for every rough initial datum is a separate endpoint. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem Q09_POST_CUTOFF_SMOOTHNESS
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    (ha : EnergySigmaZero a) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) {δ : ℝ} (hδ : cutoff a ν < δ) :
    HasSmoothTail ν u δ :=
  (TAIL_CONCLUSIONS_FROM_EXACT_ADMISSION hν
    (EXACT_H1_ADMISSION_UNCONDITIONAL ν hν) ha hu hδ).1

theorem Q11_POST_CUTOFF_ENERGY_EQUALITY
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    (ha : EnergySigmaZero a) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) {δ : ℝ} (hδ : cutoff a ν < δ) :
    TailEnergyEquality ν u G δ :=
  (TAIL_CONCLUSIONS_FROM_EXACT_ADMISSION hν
    (EXACT_H1_ADMISSION_UNCONDITIONAL ν hν) ha hu hδ).2.1

theorem Q12_POST_CUTOFF_TRACE_UNIQUENESS
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    (ha : EnergySigmaZero a) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) {δ : ℝ} (hδ : cutoff a ν < δ) :
    UniqueFuture ν u G δ :=
  (TAIL_CONCLUSIONS_FROM_EXACT_ADMISSION hν
    (EXACT_H1_ADMISSION_UNCONDITIONAL ν hν) ha hu hδ).2.2

theorem Q13_ZERO_AND_SAFE_CLOSED_CUTOFF
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    (ha : EnergySigmaZero a) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G) :
    HasSmoothTail ν u (safeCutoff a ν) :=
  SAFE_CUTOFF_TAIL hν hu (fun _ hδ => Q09_POST_CUTOFF_SMOOTHNESS hν ha hu hδ)

theorem Quasi_Fefferman_B_of_LH_existence
    (hexists : ∀ (ν : ℝ), 0 < ν → ∀ (a : CriticalPhysicalL2),
      EnergySigmaZero a →
        ∃ (u : Velocity) (G : WeakGradientTrajectory), CriticalLerayHopf ν a u G) :
    QuasiFeffermanBStatement :=
  Quasi_Fefferman_B_of_analytic_endpoints hexists EXACT_H1_ADMISSION_UNCONDITIONAL

end
end QuasiFeffermanB
