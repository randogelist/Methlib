import SingularClosure.NoetherClosure.Admission

/-! NC02: only order and normalized coercivity, no NSE estimates. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure
noncomputable section

theorem NOETHER_UNIFORM_PHYSICAL_ENSTROPHY
    (hNoether : NOETHER_CHARGE_ADMISSION)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ≥0,
      ∀ (N : ℕ), 1 ≤ N → ∀ (g : GalerkinSolution ν a N),
        ∀ t ∈ Icc (0 : ℝ) T,
          physicalEnstrophy (g.velocity t) ≤ (M : ℝ≥0∞) := by
  obtain ⟨M, hcert⟩ := hNoether ν hν a ha T hT
  refine ⟨M, ?_⟩
  intro N hN g t ht
  obtain ⟨Q, hcoercive, hdecrease, hinitial⟩ := hcert N hN g
  have hQ : Q t ≤ M := (hdecrease t ht).trans hinitial
  exact (hcoercive t ht).trans (ENNReal.coe_le_coe.mpr hQ)

end
end SingularClosure
