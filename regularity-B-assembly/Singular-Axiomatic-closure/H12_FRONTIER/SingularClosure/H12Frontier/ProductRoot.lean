import SingularClosure.H12Frontier.ProductNormalization
import SingularClosure.H12Frontier.ProductMilestones

/-! P15-P16: product-radius roots. All original datum hypotheses and the
same-solution quantitative conclusions are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

theorem FRONTIER_H12_PRODUCT_NATIVE :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : nativeProduct * ‖a‖ < ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ productDissipationConstant ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          productDerivativeConstant ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖)))  := by
  intro ν hν a ha hsmall
  obtain ⟨U, hW, hV, hQ⟩ := PRODUCT_GLOBAL_ENERGY_CLASS ν hν a ha hsmall
  obtain ⟨hLH, hUnique, hNSE, hSerrin⟩ :=
    PRODUCT_SERRIN_LERAYHOPF ν hν a hsmall U hQ
  exact ⟨PRODUCT_DATUM_AX6 ν hν a ha.reality ha.solenoidal ha.mean_zero hsmall,
    U, hLH, hUnique, hNSE, hW, hV, hSerrin, hQ⟩

theorem FRONTIER_H12_PRODUCT :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : paperNorm 1 a < (Real.sqrt 2 * paperScale ^ 3 / literatureK2) * ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ productDissipationConstant ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          productDerivativeConstant ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖))) := by
  intro ν hν a ha hsmall
  exact FRONTIER_H12_PRODUCT_NATIVE ν hν a ha
    ((PRODUCT_SMALLNESS_IFF ν a ha.mean_zero).mp hsmall)

theorem FRONTIER_H12_PRODUCT_ADAPTER_CHAIN :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : paperNorm 1 a < (Real.sqrt 2 * paperScale ^ 3 / literatureK2) * ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ productDissipationConstant ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          productDerivativeConstant ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖))) :=
  @FRONTIER_H12_PRODUCT

end
end SingularClosure.H12Frontier
