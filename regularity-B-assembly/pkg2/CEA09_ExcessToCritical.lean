import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace CEATheta

structure ExcessCriticalHorizon
    (α β V0 R0 CX CD : ℝ) where
  hα : 0 < α
  hβ : 0 ≤ β
  hV0 : 0 ≤ V0
  hR0 : 0 ≤ R0
  hCX : 0 ≤ CX
  hCD : 0 ≤ CD
  Vinit : ℕ → ℝ
  V : ℕ → ℝ
  G : ℕ → ℝ
  R : ℕ → ℝ
  X : ℕ → ℝ
  D : ℕ → ℝ
  Vinit_nonneg : ∀ m, 0 ≤ Vinit m
  V_nonneg : ∀ m, 0 ≤ V m
  G_nonneg : ∀ m, 0 ≤ G m
  R_nonneg : ∀ m, 0 ≤ R m
  X_nonneg : ∀ m, 0 ≤ X m
  D_nonneg : ∀ m, 0 ≤ D m
  initial_bound : ∀ m, Vinit m ≤ V0
  action_bound : ∀ m, R m ≤ R0
  energy : ∀ m, V m + α * G m ≤ Vinit m + β * R m
  x_compare : ∀ m, X m ≤ CX * V m
  d_compare : ∀ m, D m ≤ CD * G m

def budget (β V0 R0 : ℝ) : ℝ := V0 + β * R0

theorem budget_nonneg
    {β V0 R0 : ℝ}
    (hβ : 0 ≤ β) (hV0 : 0 ≤ V0) (hR0 : 0 ≤ R0) :
    0 ≤ budget β V0 R0 := by
  exact add_nonneg hV0 (mul_nonneg hβ hR0)

theorem moment_le_budget
    {α β V0 R0 CX CD : ℝ}
    (c : ExcessCriticalHorizon α β V0 R0 CX CD)
    (m : ℕ) :
    c.V m ≤ budget β V0 R0 := by
  have hαG : 0 ≤ α * c.G m :=
    mul_nonneg c.hα.le (c.G_nonneg m)
  have hVlhs : c.V m ≤ c.V m + α * c.G m := by
    simpa using (add_le_add_left hαG (c.V m))
  have htail :
      c.Vinit m + β * c.R m ≤ V0 + β * R0 := by
    exact add_le_add
      (c.initial_bound m)
      (mul_le_mul_of_nonneg_left (c.action_bound m) c.hβ)
  exact hVlhs.trans ((c.energy m).trans htail)

theorem dissipation_weighted_le_budget
    {α β V0 R0 CX CD : ℝ}
    (c : ExcessCriticalHorizon α β V0 R0 CX CD)
    (m : ℕ) :
    α * c.G m ≤ budget β V0 R0 := by
  have hGleft : α * c.G m ≤ c.V m + α * c.G m := by
    simpa [add_comm] using
      (add_le_add_left (c.V_nonneg m) (α * c.G m))
  have htail :
      c.Vinit m + β * c.R m ≤ V0 + β * R0 := by
    exact add_le_add
      (c.initial_bound m)
      (mul_le_mul_of_nonneg_left (c.action_bound m) c.hβ)
  exact hGleft.trans ((c.energy m).trans htail)

theorem dissipation_le_budget_div
    {α β V0 R0 CX CD : ℝ}
    (c : ExcessCriticalHorizon α β V0 R0 CX CD)
    (m : ℕ) :
    c.G m ≤ budget β V0 R0 / α := by
  exact (le_div_iff₀ c.hα).2 (by
    simpa [mul_comm] using dissipation_weighted_le_budget c m)

theorem physical_critical_pair_bound
    {α β V0 R0 CX CD : ℝ}
    (c : ExcessCriticalHorizon α β V0 R0 CX CD)
    (m : ℕ) :
    c.X m ≤ CX * budget β V0 R0 ∧
      c.D m ≤ CD * (budget β V0 R0 / α) := by
  constructor
  · exact (c.x_compare m).trans
      (mul_le_mul_of_nonneg_left (moment_le_budget c m) c.hCX)
  · exact (c.d_compare m).trans
      (mul_le_mul_of_nonneg_left (dissipation_le_budget_div c m) c.hCD)

theorem CEA_theta_to_criticalPair_scalar
    {α β V0 R0 CX CD : ℝ}
    (c : ExcessCriticalHorizon α β V0 R0 CX CD) :
    ∀ m : ℕ,
      c.X m ≤ CX * budget β V0 R0 ∧
      c.D m ≤ CD * (budget β V0 R0 / α) := by
  intro m
  exact physical_critical_pair_bound c m

#print axioms CEATheta.budget_nonneg
#print axioms CEATheta.moment_le_budget
#print axioms CEATheta.dissipation_weighted_le_budget
#print axioms CEATheta.dissipation_le_budget_div
#print axioms CEATheta.physical_critical_pair_bound
#print axioms CEATheta.CEA_theta_to_criticalPair_scalar

end CEATheta
