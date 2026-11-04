import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Scoped reconstruction from the definition. This candidate has not yet
been externally compiled or audited. -/

namespace HVRSimpleMoebiusBound

theorem abs_moebius_le_one (n : ℕ) : |ArithmeticFunction.moebius n| ≤ 1 := by
  change |(if Squarefree n then (-1 : ℤ) ^ ArithmeticFunction.cardFactors n else 0)| ≤ 1
  split_ifs
  · simp only [abs_pow, abs_neg, abs_one, one_pow, le_refl]
  · simp only [abs_zero, zero_le_one]

end HVRSimpleMoebiusBound
