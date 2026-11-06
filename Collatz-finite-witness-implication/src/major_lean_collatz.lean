import CollatzIntegerBridge

/-! A single entry point for the existing finite affine witness chain.
The referenced proofs and checker live in the bundled source modules.
There is no asserted accepted witness, implementation equivalence with C,
or proof that a witness exists. The declarations below need an external
build and theorem-level audit. -/

namespace MajorLeanCollatz

open CollatzIntegerBridge PoincareSecond

variable {d : Nat}

/-- The integer acceptance predicate agrees with the original checker. -/
theorem integer_check_iff_original (E : Encoding d) :
    integerCheck E = true ↔ 0 < E.den ∧ (decode E).check = true :=
  integerCheck_iff_original_check E

/-- The frozen witness implication targets the ordinary Collatz map. -/
theorem integer_check_implies_collatz (E : Encoding d)
    (h : integerCheck E = true) :
    ∀ n : Nat, 0 < n → OrdinaryReachesOne n :=
  integerValid_implies_collatz E ((integerCheck_eq_true_iff E).mp h)

/-- Necessary exact filter conditions: failure excludes acceptance. -/
theorem denominator_positive (E : Encoding d) (h : integerCheck E = true) :
    0 < E.den := ((integerCheck_eq_true_iff E).mp h).1

theorem b0_nonnegative (E : Encoding d) (h : integerCheck E = true) :
    nonnegative E.B0 := ((integerCheck_eq_true_iff E).mp h).2.1

theorem b1_nonnegative (E : Encoding d) (h : integerCheck E = true) :
    nonnegative E.B1 := ((integerCheck_eq_true_iff E).mp h).2.2.1

theorem seed_nonnegative (E : Encoding d) (h : integerCheck E = true) :
    ∀ i, 0 ≤ E.seed i := ((integerCheck_eq_true_iff E).mp h).2.2.2.1

theorem weight_nonnegative (E : Encoding d) (h : integerCheck E = true) :
    ∀ i, 0 ≤ E.weight i := ((integerCheck_eq_true_iff E).mp h).2.2.2.2.1

end MajorLeanCollatz
