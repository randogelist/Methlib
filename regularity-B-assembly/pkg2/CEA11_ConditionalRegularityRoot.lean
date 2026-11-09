import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace CEATheta

def horizonBudget (β V0 R0 : ℝ) : ℝ :=
  V0 + β * R0

structure CEARegularityCertificate
    (α β CX CD C6 : ℝ)
    (Regular : Prop) where
  hα : 0 < α
  hβ : 0 ≤ β
  hCX : 0 ≤ CX
  hCD : 0 ≤ CD
  hC6 : 0 ≤ C6

  V0 : ℝ → ℝ
  R0 : ℝ → ℝ
  Vinit : ℕ → ℝ → ℝ
  V : ℕ → ℝ → ℝ
  G : ℕ → ℝ → ℝ
  R : ℕ → ℝ → ℝ
  X : ℕ → ℝ → ℝ
  D : ℕ → ℝ → ℝ

  hV0 : ∀ T, 0 ≤ T → 0 ≤ V0 T
  hR0 : ∀ T, 0 ≤ T → 0 ≤ R0 T
  hVinit : ∀ m T, 0 ≤ T → 0 ≤ Vinit m T
  hV : ∀ m T, 0 ≤ T → 0 ≤ V m T
  hG : ∀ m T, 0 ≤ T → 0 ≤ G m T
  hR : ∀ m T, 0 ≤ T → 0 ≤ R m T
  hX : ∀ m T, 0 ≤ T → 0 ≤ X m T
  hD : ∀ m T, 0 ≤ T → 0 ≤ D m T

  initial_bound : ∀ m T, 0 ≤ T → Vinit m T ≤ V0 T
  action_bound : ∀ m T, 0 ≤ T → R m T ≤ R0 T

  weighted_energy :
    ∀ m T, 0 ≤ T →
      V m T + α * G m T ≤ Vinit m T + β * R m T

  critical_moment_compare :
    ∀ m T, 0 ≤ T → X m T ≤ CX * V m T

  critical_diss_compare :
    ∀ m T, 0 ≤ T → D m T ≤ CD * G m T

  H1L4 : ℝ → ℝ
  L6L4 : ℝ → ℝ

  hH1L4 : ∀ T, 0 ≤ T → 0 ≤ H1L4 T
  hL6L4 : ∀ T, 0 ≤ T → 0 ≤ L6L4 T

  critical_interpolation :
    ∀ T, 0 ≤ T →
      H1L4 T ≤
        (CX * horizonBudget β (V0 T) (R0 T)) *
        (CD * (horizonBudget β (V0 T) (R0 T) / α))

  sobolev_integrated :
    ∀ T, 0 ≤ T →
      L6L4 T ≤ C6 ^ 4 * H1L4 T

  Serrin46 : ℝ → Prop

  serrin46_of_bound :
    ∀ T, 0 ≤ T →
      L6L4 T ≤
        C6 ^ 4 *
          ((CX * horizonBudget β (V0 T) (R0 T)) *
           (CD * (horizonBudget β (V0 T) (R0 T) / α))) →
      Serrin46 T

  regular_of_all_serrin46 :
    (∀ T, 0 ≤ T → Serrin46 T) → Regular

theorem moment_budget
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular)
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    c.V m T ≤ horizonBudget β (c.V0 T) (c.R0 T) := by
  have hαG : 0 ≤ α * c.G m T :=
    mul_nonneg c.hα.le (c.hG m T hT)
  have hleft : c.V m T ≤ c.V m T + α * c.G m T := by
    simpa using add_le_add_left hαG (c.V m T)
  have htail :
      c.Vinit m T + β * c.R m T ≤
        c.V0 T + β * c.R0 T := by
    exact add_le_add
      (c.initial_bound m T hT)
      (mul_le_mul_of_nonneg_left (c.action_bound m T hT) c.hβ)
  exact hleft.trans ((c.weighted_energy m T hT).trans htail)

theorem dissipation_budget
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular)
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    c.G m T ≤ horizonBudget β (c.V0 T) (c.R0 T) / α := by
  have hleft : α * c.G m T ≤ c.V m T + α * c.G m T := by
    simpa [add_comm] using
      add_le_add_left (c.hV m T hT) (α * c.G m T)
  have htail :
      c.Vinit m T + β * c.R m T ≤
        c.V0 T + β * c.R0 T := by
    exact add_le_add
      (c.initial_bound m T hT)
      (mul_le_mul_of_nonneg_left (c.action_bound m T hT) c.hβ)
  have hweighted :
      α * c.G m T ≤ horizonBudget β (c.V0 T) (c.R0 T) := by
    exact hleft.trans ((c.weighted_energy m T hT).trans htail)
  exact (le_div_iff₀ c.hα).2 (by
    simpa [mul_comm] using hweighted)

theorem critical_pair_uniform
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular)
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    c.X m T ≤ CX * horizonBudget β (c.V0 T) (c.R0 T) ∧
    c.D m T ≤ CD * (horizonBudget β (c.V0 T) (c.R0 T) / α) := by
  constructor
  · exact (c.critical_moment_compare m T hT).trans
      (mul_le_mul_of_nonneg_left (moment_budget c m T hT) c.hCX)
  · exact (c.critical_diss_compare m T hT).trans
      (mul_le_mul_of_nonneg_left (dissipation_budget c m T hT) c.hCD)

theorem finite_horizon_L4L6_bound
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular)
    (T : ℝ) (hT : 0 ≤ T) :
    c.L6L4 T ≤
      C6 ^ 4 *
        ((CX * horizonBudget β (c.V0 T) (c.R0 T)) *
         (CD * (horizonBudget β (c.V0 T) (c.R0 T) / α))) := by
  have hCpow : 0 ≤ C6 ^ 4 := pow_nonneg c.hC6 4
  calc
    c.L6L4 T ≤ C6 ^ 4 * c.H1L4 T :=
      c.sobolev_integrated T hT
    _ ≤ C6 ^ 4 *
        ((CX * horizonBudget β (c.V0 T) (c.R0 T)) *
         (CD * (horizonBudget β (c.V0 T) (c.R0 T) / α))) :=
      mul_le_mul_of_nonneg_left (c.critical_interpolation T hT) hCpow

theorem all_horizons_serrin46
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular) :
    ∀ T, 0 ≤ T → c.Serrin46 T := by
  intro T hT
  exact c.serrin46_of_bound T hT (finite_horizon_L4L6_bound c T hT)

theorem CEA_theta_regular_conditional_root
    {α β CX CD C6 : ℝ} {Regular : Prop}
    (c : CEARegularityCertificate α β CX CD C6 Regular) :
    Regular :=
  c.regular_of_all_serrin46 (all_horizons_serrin46 c)

#print axioms CEATheta.moment_budget
#print axioms CEATheta.dissipation_budget
#print axioms CEATheta.critical_pair_uniform
#print axioms CEATheta.finite_horizon_L4L6_bound
#print axioms CEATheta.all_horizons_serrin46
#print axioms CEATheta.CEA_theta_regular_conditional_root

end CEATheta
