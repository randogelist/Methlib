import SingularClosure.NoetherClosure.SixChannelBridge

/-!
NC04: finite-window pointwise six-enstrophy gives Methlib's exact AX6 budget.
No altered AX6 proposition and no hidden analytic premise are introduced.
-/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure
noncomputable section

/-- Exact universal bridge from the named Noether research admission to AX6. -/
theorem NOETHER_TO_AX6
    (hNoether : NOETHER_CHARGE_ADMISSION) : AX6Statement := by
  intro ν hν a ha T hT
  obtain ⟨M, hbound⟩ :=
    NOETHER_UNIFORM_SIX_ENSTROPHY hNoether ν hν a ha T hT
  let timeLength : ℝ≥0 := ⟨T, le_of_lt hT⟩
  refine ⟨timeLength * M ^ 2, ?_⟩
  intro N hN g
  have hAE :
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        (sixEnstrophy N (g.coeff t)) ^ 2 ≤ (M : ℝ≥0∞) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb := hbound N hN g t ht
    simpa only [pow_two] using mul_le_mul' hb hb
  calc
    budget6 N g.coeff T =
        ∫⁻ t in Icc (0 : ℝ) T,
          (sixEnstrophy N (g.coeff t)) ^ 2 := rfl
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) T, (M : ℝ≥0∞) ^ 2 :=
      lintegral_mono_ae hAE
    _ = ((timeLength * M ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      have hTcoe : ENNReal.ofReal T =
          ((⟨T, hT.le⟩ : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal hT.le
      simp [timeLength, setLIntegral_const, Real.volume_Icc,
        ENNReal.coe_mul, ENNReal.coe_pow, hTcoe, mul_comm]

end
end SingularClosure
