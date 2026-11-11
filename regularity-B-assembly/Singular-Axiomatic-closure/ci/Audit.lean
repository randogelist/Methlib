import SingularClosure

set_option autoImplicit false
set_option Elab.async false

open Set MeasureTheory SingularClosure
open scoped BigOperators Interval ENNReal NNReal ContDiff

noncomputable section

example : SmoothSigmaZero (0 : Field) := by
  exact SingularClosure.smoothSigmaZero_zero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.smoothSigmaZero_zero"
#check @SingularClosure.smoothSigmaZero_zero
#print axioms SingularClosure.smoothSigmaZero_zero

example (ν : ℝ) :
    GlobalSmoothNSE ν (0 : Field) (0 : Velocity) (0 : Pressure) := by
  exact SingularClosure.globalSmoothNSE_zero ν

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.globalSmoothNSE_zero"
#check @SingularClosure.globalSmoothNSE_zero
#print axioms SingularClosure.globalSmoothNSE_zero

example :
    (∀ a : FourierCoeff, (∑ A : Fin 6, spectralChannel A a) = a) ∧
    (∀ (A : Fin 6) (a : FourierCoeff),
      spectralChannel A (spectralChannel A a) = spectralChannel A a) ∧
    (∀ (A B : Fin 6), A ≠ B → ∀ a : FourierCoeff,
      spectralChannel A (spectralChannel B a) = 0) := by
  exact SingularClosure.SIX_CHANNEL_SPECTRAL_PROJECTIONS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_SPECTRAL_PROJECTIONS"
#check @SingularClosure.SIX_CHANNEL_SPECTRAL_PROJECTIONS
#print axioms SingularClosure.SIX_CHANNEL_SPECTRAL_PROJECTIONS

example (A : Fin 6)
    {a : FourierCoeff} (ha : SpectralSolenoidal a) :
    SpectralSolenoidal (spectralChannel A a) := by
  exact SingularClosure.spectralChannel_preserves_solenoidal A ha

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.spectralChannel_preserves_solenoidal"
#check @SingularClosure.spectralChannel_preserves_solenoidal
#print axioms SingularClosure.spectralChannel_preserves_solenoidal

example (w : Frequency → ℝ≥0∞)
    (a : FourierCoeff) :
    (∑ A : Fin 6, spectralEnergy w (spectralChannel A a)) = spectralEnergy w a := by
  exact SingularClosure.SIX_CHANNEL_SPECTRAL_ENERGY_EQ w a

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_SPECTRAL_ENERGY_EQ"
#check @SingularClosure.SIX_CHANNEL_SPECTRAL_ENERGY_EQ
#print axioms SingularClosure.SIX_CHANNEL_SPECTRAL_ENERGY_EQ

example (a : FourierCoeff) :
    (∑ A : Fin 6, spectralEnstrophy (spectralChannel A a)) = spectralEnstrophy a := by
  exact SingularClosure.SIX_CHANNEL_SPECTRAL_ENSTROPHY_EQ a

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_SPECTRAL_ENSTROPHY_EQ"
#check @SingularClosure.SIX_CHANNEL_SPECTRAL_ENSTROPHY_EQ
#print axioms SingularClosure.SIX_CHANNEL_SPECTRAL_ENSTROPHY_EQ

example
    {y z d : ℝ → ℝ} {ν κ T M y₀ : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (h_initial : y 0 ≤ y₀)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3)
    (hbudget : (∫ s in (0 : ℝ)..T, (y s) ^ 2) ≤ M) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤ y₀ * Real.exp (κ * M) := by
  exact SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET hν hκ hT hM hy hz hd hy_nonneg h_initial hderiv hcubic hbudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET"
#check @SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET
#print axioms SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET

example
    {y z d : ℝ → ℝ} {ν κ T M : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3)
    (hbudget : (∫ s in (0 : ℝ)..T, (y s) ^ 2) ≤ M) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤ y 0 * Real.exp (κ * M) := by
  exact SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL hν hκ hT hM hy hz hd hy_nonneg hderiv hcubic hbudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL"
#check @SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL
#print axioms SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL

example (ν : ℝ) (N : ℕ) : GalerkinSolution ν (0 : Field) N := by
  exact SingularClosure.zeroGalerkinSolution ν N

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.zeroGalerkinSolution"
#check @SingularClosure.zeroGalerkinSolution
#print axioms SingularClosure.zeroGalerkinSolution

example (ν : ℝ) (N : ℕ) :
    (zeroGalerkinSolution ν N).velocity = (0 : Velocity) := by
  exact SingularClosure.zeroGalerkinSolution_velocity ν N

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.zeroGalerkinSolution_velocity"
#check @SingularClosure.zeroGalerkinSolution_velocity
#print axioms SingularClosure.zeroGalerkinSolution_velocity

example (v : Field) (x : Vec) :
    0 ≤ gradientSquareDensity v x := by
  exact SingularClosure.gradientSquareDensity_nonneg v x

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.gradientSquareDensity_nonneg"
#check @SingularClosure.gradientSquareDensity_nonneg
#print axioms SingularClosure.gradientSquareDensity_nonneg

example {N : ℕ} {c : ℝ → FourierCoeff} {T : ℝ} {M : ℝ≥0}
    (h : budget6 N c T ≤ (M : ℝ≥0∞)) :
    budget6 N c T ≠ ⊤ := by
  exact SingularClosure.budget6_ne_top_of_bound h

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.budget6_ne_top_of_bound"
#check @SingularClosure.budget6_ne_top_of_bound
#print axioms SingularClosure.budget6_ne_top_of_bound

example (N : ℕ) (a : FourierCoeff) :
    (∑ A : Fin 6, physicalChannel N A a) = finiteSynthesis N a := by
  exact SingularClosure.SIX_CHANNEL_FINITE_RECONSTRUCTION N a

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_FINITE_RECONSTRUCTION"
#check @SingularClosure.SIX_CHANNEL_FINITE_RECONSTRUCTION
#print axioms SingularClosure.SIX_CHANNEL_FINITE_RECONSTRUCTION

example (N : ℕ) (a : FourierCoeff)
    (j : Fin 3) (x : Vec) :
    coordinateDerivative (finiteSynthesis N a) j x =
      ∑ A : Fin 6, coordinateDerivative (physicalChannel N A a) j x := by
  exact SingularClosure.SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION N a j x

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION"
#check @SingularClosure.SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION
#print axioms SingularClosure.SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION

example (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (finiteGalerkinRhs ν N) := by
  exact SingularClosure.contDiff_finiteGalerkinRhs ν N

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.contDiff_finiteGalerkinRhs"
#check @SingularClosure.contDiff_finiteGalerkinRhs
#print axioms SingularClosure.contDiff_finiteGalerkinRhs

example {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        2 * (star (g.coeff t k i) * galerkinRhs ν N (g.coeff t) k i).re)
      (Ici 0) t := by
  exact SingularClosure.GalerkinSolution.coefficientEnergy_hasDerivWithinAt g ht

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientEnergy_hasDerivWithinAt"
#check @SingularClosure.GalerkinSolution.coefficientEnergy_hasDerivWithinAt
#print axioms SingularClosure.GalerkinSolution.coefficientEnergy_hasDerivWithinAt

end
