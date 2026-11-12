import SingularityDisprovement.Dyadic
import SingularityDisprovement.DyadicSums
import SingularityDisprovement.Admission
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
open SingularClosure

namespace SingularityDisprovement

noncomputable section

private theorem tsum_natAbs_double (f : ℕ → ℝ) (hf : Summable f) (hzero : f 0 = 0) :
    (∑' z : ℤ, f z.natAbs) = 2 * ∑' n : ℕ, f n := by
  have hz : Summable (fun z : ℤ => f z.natAbs) := by
    apply Summable.of_nat_of_neg
    · simpa using hf
    · simpa using hf
  have h := tsum_nat_add_neg hz
  have h' : (∑' n : ℕ, (f n + f n)) = ∑' z : ℤ, f z.natAbs := by
    simpa [hzero] using h
  rw [hf.tsum_add hf] at h'
  linarith

private theorem dyadicCoeff_off_axis (ν : ℝ) (ki : FourierIndex)
    (hki : ki ∉ Set.range shearFourierIndex) : dyadicCoeff ν ki.1 ki.2 = 0 := by
  have h : ¬ (ki.2 = 0 ∧ ki.1 0 = 0 ∧ ki.1 2 = 0) := by
    intro h
    apply hki
    refine ⟨ki.1 1, ?_⟩
    apply Prod.ext
    · exact shearFrequency_of_axis h.2.1 h.2.2
    · exact h.1.symm
  simp [dyadicCoeff, h]

theorem dyadicSeed_physical_norm_sq (ν : ℝ) :
    ‖physicalL2 (dyadicSeed ν)‖ ^ 2 = ν ^ 2 * dyadicR / 8 := by
  rw [physicalL2_eq_native,
    criticalInitialPhysicalL2_norm_sq _ (dyadicSeed_sigma ν).reality
      (dyadicSeed_sigma ν).mean_zero, dyadicSeed_coeff]
  have hindex := shearFourierIndex_injective.tsum_eq
    (f := fun ki : FourierIndex => Complex.normSq (dyadicCoeff ν ki.1 ki.2)) (by
      intro ki hki
      by_contra hnot
      exact hki (by
        change Complex.normSq (dyadicCoeff ν ki.1 ki.2) = 0
        rw [dyadicCoeff_off_axis ν ki hnot]
        simp))
  rw [← hindex]
  simp only [shearFourierIndex, dyadicCoeff_axis, Complex.normSq_eq_norm_sq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [tsum_mul_left,
    tsum_natAbs_double (fun n => dyadicAmplitude n ^ 2)
      dyadicAmplitude_sq_summable (by simp), dyadicAmplitude_sq_tsum]
  ring

theorem dyadicSeed_critical_norm_sq (ν : ℝ) :
    ‖dyadicSeed ν‖ ^ 2 = Real.pi * ν ^ 2 * dyadicS / 8 := by
  have hrepr := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (criticalSobolevRepr 1 (dyadicSeed ν))
  have hnorm : ‖dyadicSeed ν‖ ^ 2 =
      ∑' ki : FourierIndex, ‖criticalWeightedCoeff 1 (dyadicCoeff ν) ki‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      (criticalSobolevRepr 1).norm_map, criticalSobolevRepr_apply,
      dyadicSeed_coeff] using hrepr
  rw [hnorm]
  have hindex := shearFourierIndex_injective.tsum_eq
    (f := fun ki : FourierIndex => ‖criticalWeightedCoeff 1 (dyadicCoeff ν) ki‖ ^ 2) (by
      intro ki hki
      by_contra hnot
      exact hki (by simp [criticalWeightedCoeff, dyadicCoeff_off_axis ν ki hnot]))
  rw [← hindex]
  simp_rw [dyadicCoeff_weighted_axis_sq]
  rw [tsum_mul_left,
    tsum_natAbs_double (fun n => (n : ℝ) * dyadicAmplitude n ^ 2)
      dyadicAmplitude_weighted_sq_summable (by simp),
    dyadicAmplitude_weighted_sq_tsum]
  ring

theorem DYADIC_CRITICAL_DATUM (ν : ℝ) (hν : 0 < ν) :
    CriticalSigmaZero (dyadicSeed ν) ∧
    0 < ‖dyadicSeed ν‖ ∧
    ‖physicalL2 (dyadicSeed ν)‖ ^ 2 = ν ^ 2 * dyadicR / 8 ∧
    ‖dyadicSeed ν‖ ^ 2 = Real.pi * ν ^ 2 * dyadicS / 8 :=
  ⟨dyadicSeed_sigma ν, dyadicSeed_norm_pos hν,
    dyadicSeed_physical_norm_sq ν, dyadicSeed_critical_norm_sq ν⟩

end
end SingularityDisprovement
