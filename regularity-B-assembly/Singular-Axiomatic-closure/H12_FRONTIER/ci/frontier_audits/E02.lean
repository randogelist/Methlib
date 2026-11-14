import SingularClosure.H12Frontier.ConstantNormalization

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    0 < literatureK2 ∧ 0 < frontierConstant ∧
    literatureK2 = Real.sqrt 2 * CSHalf * CSOne * CSZero / (2 * Real.pi) ∧
    frontierConstant = literatureK2 / (2 * Real.sqrt Real.pi) ∧
    (∀ a : CriticalSobolev 1, SpectralMeanZero (criticalCoeff 1 a) →
      frontierConstant * ‖a‖ = (literatureK2 / Real.sqrt 2) * paperNorm 1 a) ∧
    (∀ ν A B d : ℝ, 0 ≤ A →
      ((d / (4 * Real.pi) +
        (ν - literatureK2 * Real.sqrt (A / (4 * Real.pi))) * (B / (2 * Real.pi)) ≤ 0) ↔
      (d + 2 * (ν - frontierConstant * Real.sqrt A) * B ≤ 0))) :=
  @SingularClosure.H12Frontier.FRONTIER_H12_CONSTANT_NORMALIZATION

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.FRONTIER_H12_CONSTANT_NORMALIZATION"
#print axioms SingularClosure.H12Frontier.FRONTIER_H12_CONSTANT_NORMALIZATION

end
end SingularClosure.H12Frontier
