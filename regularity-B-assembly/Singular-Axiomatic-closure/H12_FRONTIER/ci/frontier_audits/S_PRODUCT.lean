import SingularClosure.H12Frontier.ExplicitNonlinear
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace SingularClosure.H12Frontier
noncomputable section

example (N : ℕ) (c : FourierCoeff)
    (hs : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hr : SpectralReality c) (hd : SpectralSolenoidal c) :
    |criticalNonlinearPower 1 N c| ≤
      nativeProduct * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  EXPLICIT_PRODUCT_NONLINEAR_BOUND N c hs hr hd
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.EXPLICIT_PRODUCT_NONLINEAR_BOUND"
#print axioms SingularClosure.H12Frontier.EXPLICIT_PRODUCT_NONLINEAR_BOUND

example (N : ℕ) (c : FourierCoeff) :
    eLpNorm (finiteSynthesis N c) 3 (volume.restrict unitCube) ≤
      ENNReal.ofReal nativeThree *
        (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) :=
  nativeHalf_bound N c
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.nativeHalf_bound"
#print axioms SingularClosure.H12Frontier.nativeHalf_bound

example : 0 < nativeProduct := nativeProduct_pos
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.nativeProduct_pos"
#print axioms SingularClosure.H12Frontier.nativeProduct_pos
end
end SingularClosure.H12Frontier
