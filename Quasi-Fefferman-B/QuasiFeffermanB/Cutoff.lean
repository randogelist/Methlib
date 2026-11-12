import QuasiFeffermanB.Semantics

/-! Exact scalar cutoff identities. These do not assert PDE regularity. -/
set_option autoImplicit false
set_option Elab.async true

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem CUTOFF_NONNEG (a : CriticalPhysicalL2) {ν : ℝ} (hν : 0 < ν) :
    0 ≤ cutoff a ν := by
  unfold cutoff
  positivity

theorem CUTOFF_ZERO (ν : ℝ) : cutoff (0 : CriticalPhysicalL2) ν = 0 := by
  simp [cutoff]

theorem CUTOFF_POS (a : CriticalPhysicalL2) (ha : a ≠ 0)
    {ν : ℝ} (hν : 0 < ν) : 0 < cutoff a ν := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  unfold cutoff
  positivity

theorem SAFE_CUTOFF_GT (a : CriticalPhysicalL2) (ha : a ≠ 0)
    {ν : ℝ} (hν : 0 < ν) : cutoff a ν < safeCutoff a ν := by
  have h := CUTOFF_POS a ha hν
  unfold safeCutoff
  linarith

theorem ENERGY_SLICE_CUTOFF (a : CriticalPhysicalL2) (ν E : ℝ)
    (hE : ‖a‖ ^ 2 / 2 = E) :
    cutoff a ν = E ^ 2 / (2 * Real.pi ^ 2 * ν ^ 5) := by
  rw [← hE]
  unfold cutoff
  ring

end
end QuasiFeffermanB
