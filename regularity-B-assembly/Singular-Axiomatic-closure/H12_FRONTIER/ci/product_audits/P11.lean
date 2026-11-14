import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν),
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
  @SingularClosure.H12Frontier.PRODUCT_GLOBAL_COMPACTNESS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GLOBAL_COMPACTNESS"
#print axioms SingularClosure.H12Frontier.PRODUCT_GLOBAL_COMPACTNESS

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L :=
  @SingularClosure.H12Frontier.PRODUCT_POSITIVE_ENSTROPHY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_POSITIVE_ENSTROPHY"
#print axioms SingularClosure.H12Frontier.PRODUCT_POSITIVE_ENSTROPHY

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
        (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ S :=
  @SingularClosure.H12Frontier.PRODUCT_POSITIVE_H2

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_POSITIVE_H2"
#print axioms SingularClosure.H12Frontier.PRODUCT_POSITIVE_H2

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  @SingularClosure.H12Frontier.PRODUCT_POSITIVE_ALL_ORDERS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_POSITIVE_ALL_ORDERS"
#print axioms SingularClosure.H12Frontier.PRODUCT_POSITIVE_ALL_ORDERS

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)),
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t :=
  @SingularClosure.H12Frontier.PRODUCT_POSITIVE_FLOW

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_POSITIVE_FLOW"
#print axioms SingularClosure.H12Frontier.PRODUCT_POSITIVE_FLOW

end
end SingularClosure.H12Frontier
