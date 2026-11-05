import ConcreteABCDUnifiedClosure

set_option autoImplicit false

namespace Fefferman.ConcreteReal

noncomputable section

/-- Restart the ambient velocity and pressure at time `τ`. -/
def shiftSolution (s : Solution realAnalysis) (τ : ℝ) : Solution realAnalysis where
  velocity := fun x t => s.velocity x (t + τ)
  pressure := fun x t => s.pressure x (t + τ)

/-- The datum of the restarted trajectory. -/
def shiftInitial (s : Solution realAnalysis) (τ : ℝ) : Initial realAnalysis :=
  fun x => s.velocity x τ

theorem shift_clause01 (ν : PositiveViscosity realAnalysis)
    (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : clause01 realAnalysis ν (zeroForce realAnalysis) s) :
    clause01 realAnalysis ν (zeroForce realAnalysis) (shiftSolution s τ) := by
  intro x t ht i
  change deriv (fun r : ℝ => s.velocity x (r + τ) i) t + _ = _
  rw [deriv_comp_add_const (fun r : ℝ => s.velocity x r i) τ t]
  exact h x (t + τ) (add_nonneg ht hτ) i

theorem shift_clause02 (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : clause02 realAnalysis s) :
    clause02 realAnalysis (shiftSolution s τ) := by
  intro x t ht
  exact h x (t + τ) (add_nonneg ht hτ)

theorem shift_clause03 (s : Solution realAnalysis) (τ : ℝ) :
    clause03 realAnalysis (shiftInitial s τ) (shiftSolution s τ) := by
  intro x
  change s.velocity x (0 + τ) = s.velocity x τ
  rw [zero_add]

theorem shift_clause07 (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : clause07 realAnalysis s) :
    clause07 realAnalysis (shiftSolution s τ) := by
  rcases h with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  exact hbound (t + τ) (add_nonneg ht hτ)

end

end Fefferman.ConcreteReal

#print axioms Fefferman.ConcreteReal.shift_clause01
#print axioms Fefferman.ConcreteReal.shift_clause02
#print axioms Fefferman.ConcreteReal.shift_clause03
#print axioms Fefferman.ConcreteReal.shift_clause07
