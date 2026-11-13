import SingularClosure.H12Frontier.LiteratureConstants
import SingularClosure.H12Frontier.ReplayCompactness

/-! Native-product certificate, fixed-instance constants, and quantitative budgets. -/
set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure.H12Frontier
noncomputable section

/-- P01: the actual finite NSE pairing has the positive native-product certificate. -/
theorem PRODUCT_CERTIFICATE :
    0 < nativeProduct ∧ nativeProductCertificate.constant = nativeProduct ∧
    ∀ (N : ℕ) (c : FourierCoeff),
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      |criticalNonlinearPower 1 N c| ≤
        nativeProduct * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  ⟨nativeProduct_pos, rfl, EXPLICIT_PRODUCT_NONLINEAR_BOUND⟩

theorem product_literatureK2_eq :
    literatureK2 = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct := by
  have hp : 2 * Real.sqrt Real.pi ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)).ne'
  have h := frontierConstant_eq_nativeProduct
  change literatureK2 / (2 * Real.sqrt Real.pi) = paperScale ^ 3 * nativeProduct at h
  have heq := (div_eq_iff hp).mp h
  calc
    literatureK2 = (paperScale ^ 3 * nativeProduct) * (2 * Real.sqrt Real.pi) := heq
    _ = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct := by ring

/-- P02: the comparison uses the unchanged, fixed project K2 instance. -/
theorem PRODUCT_CONSTANT_IDENTITY :
    0 < nativeProduct ∧ 0 < literatureK2 ∧
    frontierConstant = paperScale ^ 3 * nativeProduct ∧
    literatureK2 = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct :=
  ⟨nativeProduct_pos, literatureK2_pos,
    frontierConstant_eq_nativeProduct, product_literatureK2_eq⟩

def productDissipationConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.dissipationConstant nativeProductCertificate ν a

def productDerivativeConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.derivativeConstant nativeProductCertificate ν a

theorem productDissipationConstant_eq (ν : ℝ) (a : CriticalSobolev 1) :
    productDissipationConstant ν a = ‖a‖ ^ 2 / (2 * (ν - nativeProduct * ‖a‖)) :=
  rfl

theorem productDerivativeConstant_eq (ν : ℝ) (a : CriticalSobolev 1) :
    productDerivativeConstant ν a =
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) :=
  rfl

/-- P05: positive product margin and exact certificate-dependent bounds. -/
theorem PRODUCT_MARGIN_AND_BUDGETS (ν : ℝ) (a : CriticalSobolev 1)
    (hsmall : nativeProduct * ‖a‖ < ν) :
    0 < ν - nativeProduct * ‖a‖ ∧
    0 ≤ productDissipationConstant ν a ∧
    0 ≤ productDerivativeConstant ν a ∧
    productDissipationConstant ν a = ‖a‖ ^ 2 / (2 * (ν - nativeProduct * ‖a‖)) ∧
    productDerivativeConstant ν a =
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) := by
  refine ⟨sub_pos.mpr hsmall, ?_, ?_, rfl, rfl⟩
  · exact Replay.dissipationConstant_nonneg nativeProductCertificate a hsmall
  · exact Replay.derivativeConstant_nonneg nativeProductCertificate a hsmall

end
end SingularClosure.H12Frontier
