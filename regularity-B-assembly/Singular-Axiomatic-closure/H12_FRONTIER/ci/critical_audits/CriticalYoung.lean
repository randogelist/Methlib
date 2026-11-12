import SingularClosure.CriticalYoung

set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators
namespace SingularClosure
noncomputable section

example (ν A U W D : ℝ) (hν : 0 < ν) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hD : 0 ≤ D) :
    A * U * Real.sqrt W * Real.sqrt (D + W) * D ≤
      (ν / 2) * D ^ 2 +
        (8 * A ^ 4 * U ^ 4 / ν ^ 3 + A ^ 2 * U ^ 2 / ν) * W ^ 2 :=
  @SingularClosure.CRITICAL_TRANSPORT_YOUNG ν A U W D hν hA hU hW hD

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_TRANSPORT_YOUNG"
#check @SingularClosure.CRITICAL_TRANSPORT_YOUNG
#print axioms SingularClosure.CRITICAL_TRANSPORT_YOUNG

end
end SingularClosure
