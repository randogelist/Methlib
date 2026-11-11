import SingularClosure.CriticalQuantitative
import SingularClosure.CriticalPositiveFlow

/-! Literal physical time derivatives and quantitative critical representatives. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem CriticalPositiveSobolevFlow.timeDerivative_fourierCoeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    datumFourierCoeff (timeDerivative L.velocity t) = fullFourierRhs ν (L.state 0 t) := by
  rw [L.velocity_timeDerivative t ht]
  apply datumFourierCoeff_smoothFourierSynthesis
  · intro i
    apply ALL_SOBOLEV_IMP_RAPID_SCALAR _ _ i
    intro s
    rw [← L.rhs_coeff s t ht]
    exact (fourierSobolevRhs ν s (L.state (s + 2) t)).property
  · exact fullFourierRhs_reality ν (L.state 0 t) (L.state_all_mem t ht)
      (L.reality t ht) (L.solenoidal t ht)

theorem critical_ae_positive_on_Icc (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), 0 < t := by
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ht.1

/-- The representative is that of the actual physical time derivative,
identified by literal normalized-cube Fourier integration. -/
theorem critical_negative_representative_physical
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (u : ℝ → CriticalSobolev 1)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (V : ℝ → CriticalSobolev (-1))
    (hV : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff (-1) (V t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t))) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative L.velocity t) := by
  filter_upwards [hV, critical_ae_positive_on_Icc T] with t hVt ht
  rw [L.timeDerivative_fourierCoeff t ht]
  have heq : L.state 0 t = criticalToTorusH0 1 (by norm_num) (u t) := by
    apply Subtype.ext
    rw [criticalToTorusH0_coeff]
    exact hL t ht
  rw [heq]
  exact hVt

theorem SMALL_DATA_LIMIT_PHYSICAL_NEGATIVE_HALF
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative L.velocity t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ criticalTimeDerivativeBudget ν a := by
  obtain ⟨V, hV, hVc, hVb⟩ := SMALL_DATA_LIMIT_NEGATIVE_HALF ν hν a hreal hsmall
    φ hφ g u T hT hu hconv
  exact ⟨V, hV, critical_negative_representative_physical L u hL T V hVc, hVb⟩

end
end SingularClosure
