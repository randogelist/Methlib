import SingularClosure.CriticalEnergy
import SingularClosure.CriticalGalerkin

/-! The actual finite critical initial energy is bounded by the norm of
the original rough Sobolev datum. No smooth representative is assumed. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open scoped BigOperators ENNReal

namespace SingularClosure

theorem criticalEnergy_cutoffCoeff (q N : ℕ) (c : FourierCoeff) :
    criticalEnergy q N (cutoffCoeff N c) = criticalEnergy q N c := by
  unfold criticalEnergy
  apply Finset.sum_congr rfl
  intro k hk
  simp only [cutoffCoeff, if_pos hk]

/-- Finite sums of the literal weighted Fourier coordinates are bounded
by the Hilbert norm of the original coefficient datum. -/
theorem criticalEnergy_le_norm_sq (q N : ℕ) (a : CriticalSobolev (q : ℤ)) :
    criticalEnergy q N (criticalCoeff (q : ℤ) a) ≤ ‖a‖ ^ 2 := by
  classical
  have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
    (criticalSobolevRepr (q : ℤ) a) ((cutoffModes N).product (Finset.univ : Finset (Fin 3)))
  have h' :
      (∑ ki ∈ (cutoffModes N).product (Finset.univ : Finset (Fin 3)),
        ‖criticalWeightedCoeff (q : ℤ) (criticalCoeff (q : ℤ) a) ki‖ ^ 2) ≤ ‖a‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      criticalSobolevRepr_apply, (criticalSobolevRepr (q : ℤ)).norm_map] using h
  have hterm (ki : FourierIndex) :
      ‖criticalWeightedCoeff (q : ℤ) (criticalCoeff (q : ℤ) a) ki‖ ^ 2 =
        criticalFrequencyWeight ki.1 ^ q *
          Complex.normSq (criticalCoeff (q : ℤ) a ki.1 ki.2) := by
    rw [criticalWeightedCoeff_norm, mul_pow, criticalHalfWeight_zpow_sq,
      zpow_natCast, Complex.normSq_eq_norm_sq]
  simp_rw [hterm] at h'
  rw [Finset.sum_product] at h'
  exact h'

/-- The existing finite ODE, initialized from the actual rough Fourier
cutoff, inherits the datum's critical norm bound. -/
theorem criticalGalerkin_criticalEnergy_initial_le
    {ν : ℝ} {N : ℕ} (q : ℕ) (a : CriticalSobolev (q : ℤ))
    (hreal : SpectralReality (criticalCoeff (q : ℤ) a))
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff (q : ℤ) a)) N) :
    criticalEnergy q N (g.coeff 0) ≤ ‖a‖ ^ 2 := by
  rw [criticalGalerkin_initial_coeff hreal g, criticalEnergy_cutoffCoeff]
  exact criticalEnergy_le_norm_sq q N a

end SingularClosure
