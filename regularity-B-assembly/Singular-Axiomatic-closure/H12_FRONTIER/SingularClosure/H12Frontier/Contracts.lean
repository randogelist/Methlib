import SingularClosure.CriticalNonlinear
import SingularClosure.SmallDataAX6

/-! The quantitative interface contains the literal finite NSE pairing. -/
set_option autoImplicit false
set_option Elab.async true
namespace SingularClosure.H12Frontier
noncomputable section

structure NonlinearCertificate where
  constant : ℝ
  positive : 0 < constant
  bound : ∀ (N : ℕ) (c : FourierCoeff),
    (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
    SpectralReality c → SpectralSolenoidal c →
    |criticalNonlinearPower 1 N c| ≤
      constant * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c

def NonlinearCertificate.enlarge (κ : NonlinearCertificate)
    (C : ℝ) (hC : κ.constant ≤ C) : NonlinearCertificate where
  constant := C
  positive := κ.positive.trans_le hC
  bound N c hs hr hd := (κ.bound N c hs hr hd).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))
      (criticalEnergy_nonneg 3 N c))

end
end SingularClosure.H12Frontier
