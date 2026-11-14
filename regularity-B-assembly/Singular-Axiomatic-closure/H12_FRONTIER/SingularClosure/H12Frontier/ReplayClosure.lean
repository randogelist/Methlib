import SingularClosure.H12Frontier.ReplayQuantitative
import SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem globalEnergyClass (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : cert.constant * ‖a‖ < ν) :
    ∃ U : CriticalRegularSolution ν a,
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (dissipationConstant cert) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (derivativeConstant cert) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - cert.constant * ‖a‖))) := by
  obtain ⟨U, hW, hV, hquartic⟩ :=
    (quantitativeRegularity cert) ν hν a ha hsmall
  obtain ⟨hWglobal, hVglobal⟩ := U.global_energy_class
    ((dissipationConstant cert) ν a) ((derivativeConstant cert) ν a)
    ((dissipationConstant_nonneg cert) a hsmall)
    ((derivativeConstant_nonneg cert) a hsmall) hW hV
  exact ⟨U, hWglobal, hVglobal, hquartic⟩

theorem fullClosure (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : cert.constant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (dissipationConstant cert) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (derivativeConstant cert) ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - cert.constant * ‖a‖))) := by
  obtain ⟨U, hW, hV, hQ⟩ :=
    (globalEnergyClass cert) ν hν a ha hsmall
  have hδ : 0 < ν - cert.constant * ‖a‖ := sub_pos.mpr hsmall
  have hM : 0 ≤ ‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖)) :=
    div_nonneg (by positivity) (by positivity)
  have hS := U.serrin_global_memLp_of_quartic_budget
    (‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖))) hM
    (fun T hT => ⟨(hQ T hT).1, (hQ T hT).2.trans
      (div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (by positivity))⟩)
  have hSloc (T : ℝ) (hT : 0 < T) :
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)) :=
    U.serrin_time_memLp T (hQ T hT).1
  exact ⟨(datumAX6 cert) ν hν a ha.reality ha.solenoidal ha.mean_zero hsmall,
    U, U.lerayHopf_of_quartic (fun T hT => (hQ T hT).1),
    U.lerayHopfUnique_of_serrin hν hSloc, U.physicalNSE, hW, hV, hS.1, hQ⟩

end
end SingularClosure.H12Frontier.Replay
