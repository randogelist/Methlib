import QuasiFeffermanB.EnergyDatumApproximation
import SingularClosure.SobolevLimitInitial

/-! QFB endpoint extraction R4. Candidate proof bodies; external compilation
and theorem-level axiom audit are pending. The mathematical derivation is
recorded in QUASI_FEFFERMAN_B_METHLIB_COMPOSED_COMPLETION_B_TIER.txt. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem ENERGY_GALERKIN_LIMIT_INITIAL_COEFFICIENTS
    (ν : ℝ) (hν : 0 ≤ ν) (a : EnergyDatum)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (c : FourierCoeff)
    (h0 : ∀ k i, Tendsto
      (fun n => (energyDatumGalerkinFamily ν hν a (σ n)).coeff 0 k i)
      atTop (𝓝 (c k i))) :
    c = datumFourierCoeff (a.val : Field) := by
  funext k i
  have heq :
      (fun n => (energyDatumGalerkinFamily ν hν a (σ n)).coeff 0 k i)
        =ᶠ[atTop] (fun _ => datumFourierCoeff (a.val : Field) k i) := by
    by_cases hk : k = 0
    · subst k
      apply Filter.Eventually.of_forall
      intro n
      rw [energyDatumGalerkinFamily_initial]
      simp only [cutoffCoeff, if_neg (cutoffModes_zero_not_mem _),
        Pi.zero_apply, a.property.fourier_constraints.2.2 i]
    · filter_upwards [eventually_mem_cutoffModes_strictMono σ hσ k hk] with n hn
      rw [energyDatumGalerkinFamily_initial]
      simp only [cutoffCoeff, if_pos hn]
  exact tendsto_nhds_unique (h0 k i) (tendsto_const_nhds.congr' heq.symm)

end
end QuasiFeffermanB
