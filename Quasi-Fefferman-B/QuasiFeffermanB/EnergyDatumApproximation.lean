import QuasiFeffermanB.SpatialAdmission
import QuasiFeffermanB.PhysicalFourierL2
import QuasiFeffermanB.EnergyLimitCompatibility
import SingularClosure.CriticalInitialEnergy

/-! Actual Galerkin approximations of every physical L2 solenoidal mean-zero
datum. The family and its spacetime compactness are constructed, with no
analytic admission or Galerkin existence witness among the premises. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def energyDatumGalerkinFamily (ν : ℝ) (hν : 0 ≤ ν) (a : EnergyDatum) (n : ℕ) :
    GalerkinSolution ν
      (finiteSynthesis (n + 1) (datumFourierCoeff (a.val : Field))) (n + 1) :=
  criticalGalerkinSolution ν hν (datumFourierCoeff (a.val : Field))
    a.property.fourier_constraints.1 a.property.fourier_constraints.2.1 (n + 1)

theorem energyDatumGalerkinFamily_initial
    (ν : ℝ) (hν : 0 ≤ ν) (a : EnergyDatum) (n : ℕ) :
    (energyDatumGalerkinFamily ν hν a n).coeff 0 =
      cutoffCoeff (n + 1) (datumFourierCoeff (a.val : Field)) :=
  criticalGalerkinSolution_initial ν hν (datumFourierCoeff (a.val : Field))
    a.property.fourier_constraints.1 a.property.fourier_constraints.2.1 (n + 1)

theorem energyDatumGalerkinFamily_energy_initial
    (ν : ℝ) (hν : 0 ≤ ν) (a : EnergyDatum) (n : ℕ) :
    coefficientEnergy (n + 1) ((energyDatumGalerkinFamily ν hν a n).coeff 0) ≤
      ‖a.val‖ ^ 2 := by
  rw [energyDatumGalerkinFamily_initial]
  have hcut :
      coefficientEnergy (n + 1) (cutoffCoeff (n + 1) (datumFourierCoeff (a.val : Field))) =
        coefficientEnergy (n + 1) (datumFourierCoeff (a.val : Field)) := by
    simpa only [criticalEnergy, pow_zero, one_mul, coefficientEnergy] using
      criticalEnergy_cutoffCoeff 0 (n + 1) (datumFourierCoeff (a.val : Field))
  rw [hcut]
  have hb := physicalL2_coefficientEnergy_le (n + 1) (a.val : Field) (Lp.memLp a.val)
  have he : physicalEnergy (a.val : Field) = ‖a.val‖ ^ 2 := by
    rw [physicalEnergy_eq_toLp_norm_sq (a.val : Field) (Lp.memLp a.val), Lp.toLp_coeFn]
  exact hb.trans_eq he

/-- Every actual finite-energy datum has a uniformly energy-bounded Galerkin
family with an actual common modal and strong spacetime-L2 limit on [0,T]. -/
theorem ENERGY_DATUM_GALERKIN_COMPACTNESS
    (ν : ℝ) (hν : 0 < ν) (a : EnergyDatum) (T : ℝ) (hT : 0 ≤ T) :
    ∃ u : Icc (0 : ℝ) T → TorusSobolev 0, ∃ v : EnergyTimeH0L2 T,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ t, ‖u t‖ ≤ ‖a.val‖) ∧
      (∀ k i, TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          ((energyDatumGalerkinFamily ν hν.le a (φ n)).sobolevState 0 t.val).val k i)
        (fun t => (u t).val k i) atTop) ∧
      Tendsto (fun n => (energyDatumGalerkinFamily ν hν.le a (φ n)).energyTimeH0L2 T)
        atTop (𝓝 v) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
        v t = u ⟨t, ht⟩) := by
  exact ENERGY_GALERKIN_COMPATIBLE_L2H0_SUBSEQUENCE ν hν
    (fun n => finiteSynthesis (n + 1) (datumFourierCoeff (a.val : Field)))
    (fun n => n + 1) (energyDatumGalerkinFamily ν hν.le a)
    ‖a.val‖ T (norm_nonneg _) hT
    (energyDatumGalerkinFamily_energy_initial ν hν.le a)

end
end QuasiFeffermanB

