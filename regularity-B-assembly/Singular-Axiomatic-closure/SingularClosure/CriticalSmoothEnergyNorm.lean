import SingularClosure.CriticalSmoothParseval

/-! The literal physical cube energy of the smooth realization is its actual
order-zero Fourier Hilbert norm, including an arbitrary zero Fourier mode. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem critical_smoothFourierSynthesis_energy_eq_norm_sq
    (c : FourierCoeff) (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) (w : CriticalSobolev 0)
    (hw : criticalCoeff 0 w = c) :
    physicalEnergy (smoothFourierSynthesis c) = ‖w‖ ^ 2 := by
  have hs : Summable (fun ki : FourierIndex => Complex.normSq (c ki.1 ki.2)) := by
    have h := (criticalCoeff_mem 0 w).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, criticalWeightedCoeff,
      zpow_zero, one_mul, hw, Complex.normSq_eq_norm_sq] using h
  have hcomp (i : Fin 3) : Summable (fun k : Frequency => Complex.normSq (c k i)) :=
    hs.comp_injective (i := fun k : Frequency => (k, i))
      (fun k l h => congrArg Prod.fst h)
  calc
    _ = ∑ i : Fin 3, ∫ x in unitCube, (smoothFourierSynthesis c x i) ^ 2 := by
      unfold physicalEnergy
      exact integral_finsetSum Finset.univ (fun i _ =>
        (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
          (smoothFourierSynthesis_contDiff c hc).continuous).pow 2).
            continuousOn.integrableOn_compact isCompact_unitCube)
    _ = ∑ i : Fin 3, ∑' k : Frequency, Complex.normSq (c k i) := by
      exact Finset.sum_congr rfl (fun i _ =>
        critical_smoothFourierSynthesis_component_parseval c hc hreal i)
    _ = ∑' k : Frequency, ∑ i : Fin 3, Complex.normSq (c k i) :=
      (Summable.tsum_finsetSum (fun i _ => hcomp i)).symm
    _ = ∑' ki : FourierIndex, Complex.normSq (c ki.1 ki.2) := by
      simpa only [tsum_fintype] using hs.tsum_prod.symm
    _ = ‖w‖ ^ 2 := by
      rw [criticalSobolev_norm_sq, hw]
      simp only [zpow_zero, one_mul]

end

end SingularClosure
