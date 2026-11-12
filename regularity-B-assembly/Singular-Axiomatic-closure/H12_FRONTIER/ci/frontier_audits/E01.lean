import SingularClosure.H12Frontier.Normalization
set_option autoImplicit false
set_option Elab.async false
namespace SingularClosure.H12Frontier
noncomputable section

example (q : ℕ) (a : CriticalSobolev (q : ℤ))
    (hz : SpectralMeanZero (criticalCoeff (q : ℤ) a)) :
    ‖a‖ ^ 2 = (2 * Real.pi) ^ q * paperNormSq q a ∧
      paperNorm q a ^ 2 = paperNormSq q a ∧
      ‖a‖ = Real.sqrt ((2 * Real.pi) ^ q) * paperNorm q a :=
  FRONTIER_H12_NORM_BRIDGE q a hz

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.FRONTIER_H12_NORM_BRIDGE"
#print axioms SingularClosure.H12Frontier.FRONTIER_H12_NORM_BRIDGE
end
end SingularClosure.H12Frontier
