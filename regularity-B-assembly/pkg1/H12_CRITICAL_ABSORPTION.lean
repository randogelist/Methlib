import H12_SPECTRAL_ENERGY_BRIDGE

set_option autoImplicit false

noncomputable section

namespace H12CriticalAbsorption

/-- The bootstrap critical radius `ν/(4C)`. -/
def criticalRadius (ν C : ℝ) : ℝ :=
  ν / (4 * C)

/-- The conservative initial radius `ν/(8C)`. -/
def initialRadius (ν C : ℝ) : ℝ :=
  ν / (8 * C)

theorem criticalRadius_pos
    {ν C : ℝ} (hν : 0 < ν) (hC : 0 < C) :
    0 < criticalRadius ν C := by
  unfold criticalRadius
  positivity

theorem initialRadius_pos
    {ν C : ℝ} (hν : 0 < ν) (hC : 0 < C) :
    0 < initialRadius ν C := by
  unfold initialRadius
  positivity

/-- The chosen initial radius lies strictly inside the bootstrap radius. -/
theorem initialRadius_lt_criticalRadius
    {ν C : ℝ} (hν : 0 < ν) (hC : 0 < C) :
    initialRadius ν C < criticalRadius ν C := by
  unfold initialRadius criticalRadius
  have h8 : 0 < 8 * C := by positivity
  have h4 : 0 < 4 * C := by positivity
  apply (div_lt_div_iff₀ h8 h4).2
  nlinarith

/--
An initial datum below `ν/(8C)` is automatically inside the
`ν/(4C)` bootstrap region.
-/
theorem initialSmall_implies_bootstrapSmall
    {ν C E : ℝ}
    (hν : 0 < ν) (hC : 0 < C)
    (hE : 0 ≤ E)
    (hsmall : E < initialRadius ν C) :
    E ≤ criticalRadius ν C := by
  have h8 : 0 < 8 * C := by positivity
  have h4 : 0 < 4 * C := by positivity
  have h8ineq : E * (8 * C) < ν := by
    exact (lt_div_iff₀ h8).mp (by simpa [initialRadius] using hsmall)
  apply (le_div_iff₀ h4).2
  nlinarith

/--
Core critical absorption:
if `E ≤ ν/(4C)` then `C E D² ≤ (ν/4) D²`.
-/
theorem critical_nonlinearity_absorbed
    {ν C E D : ℝ}
    (hν : 0 < ν) (hC : 0 < C)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hsmall : E ≤ criticalRadius ν C) :
    C * E * D ^ 2 ≤ (ν / 4) * D ^ 2 := by
  have h4 : 0 < 4 * C := by positivity
  have hCE : C * E ≤ ν / 4 := by
    have hmul : E * (4 * C) ≤ ν := by
      exact (le_div_iff₀ h4).mp (by simpa [criticalRadius] using hsmall)
    nlinarith
  exact mul_le_mul_of_nonneg_right hCE (sq_nonneg D)

/--
If a critical energy law has nonlinear right-hand side `C E D²`,
the bootstrap region absorbs three quarters of the viscosity.
-/
theorem absorbed_energy_inequality
    {ν C E D L : ℝ}
    (hν : 0 < ν) (hC : 0 < C)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hsmall : E ≤ criticalRadius ν C)
    (henergy : L + ν * D ^ 2 ≤ C * E * D ^ 2) :
    L + (3 * ν / 4) * D ^ 2 ≤ 0 := by
  have habs :=
    critical_nonlinearity_absorbed hν hC hE hD hsmall
  nlinarith

/-- In particular the energy derivative term is nonpositive. -/
theorem energy_term_nonpositive
    {ν C E D L : ℝ}
    (hν : 0 < ν) (hC : 0 < C)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hsmall : E ≤ criticalRadius ν C)
    (henergy : L + ν * D ^ 2 ≤ C * E * D ^ 2) :
    L ≤ 0 := by
  have h :=
    absorbed_energy_inequality hν hC hE hD hsmall henergy
  have hvisc : 0 ≤ (3 * ν / 4) * D ^ 2 := by positivity
  linarith

structure CriticalAbsorptionBundle : Prop where
  initialInside :
    ∀ {ν C E : ℝ},
      0 < ν → 0 < C → 0 ≤ E →
      E < initialRadius ν C →
      E ≤ criticalRadius ν C
  absorb :
    ∀ {ν C E D : ℝ},
      0 < ν → 0 < C → 0 ≤ E → 0 ≤ D →
      E ≤ criticalRadius ν C →
      C * E * D ^ 2 ≤ (ν / 4) * D ^ 2
  energy :
    ∀ {ν C E D L : ℝ},
      0 < ν → 0 < C → 0 ≤ E → 0 ≤ D →
      E ≤ criticalRadius ν C →
      L + ν * D ^ 2 ≤ C * E * D ^ 2 →
      L + (3 * ν / 4) * D ^ 2 ≤ 0

theorem H12_CRITICAL_ABSORPTION : CriticalAbsorptionBundle :=
  ⟨initialSmall_implies_bootstrapSmall,
    critical_nonlinearity_absorbed,
    absorbed_energy_inequality⟩

end H12CriticalAbsorption
