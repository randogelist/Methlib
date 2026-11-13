import SingularClosure.H12Frontier.ProductConstants

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    0 < nativeProduct ∧ nativeProductCertificate.constant = nativeProduct ∧
    ∀ (N : ℕ) (c : FourierCoeff),
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      |criticalNonlinearPower 1 N c| ≤
        nativeProduct * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  @SingularClosure.H12Frontier.PRODUCT_CERTIFICATE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_CERTIFICATE"
#print axioms SingularClosure.H12Frontier.PRODUCT_CERTIFICATE

end
end SingularClosure.H12Frontier
