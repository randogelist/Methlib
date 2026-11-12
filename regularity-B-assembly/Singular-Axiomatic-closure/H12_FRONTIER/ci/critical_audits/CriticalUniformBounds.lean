import SingularClosure.CriticalUniformBounds

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖a‖) ∧
      ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0) ∧
      (∀ T : ℝ, TendstoUniformlyOn
        (fun n t => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ u1 : TimeH1L2 T,
        Tendsto
          (fun n => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).criticalTimeH1L2 T)
          atTop (𝓝 u1) :=
  @SingularClosure.SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS ν hν a hreal hsol hsmall

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS"
#check @SingularClosure.SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS
#print axioms SingularClosure.SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS

end
end SingularClosure
