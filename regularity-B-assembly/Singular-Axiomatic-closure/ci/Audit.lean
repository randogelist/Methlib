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


open Metric

example : ∀ (N : ℕ) (a : FourierCoeff)
    (j : Fin 3),
    coordinateDerivative (finiteSynthesis N a) j =
      finiteSynthesis N (spectralMultiplier (derivativeSymbol j) a) :=
  @SingularClosure.finiteSynthesis_coordinateDerivative

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.finiteSynthesis_coordinateDerivative"
#check @SingularClosure.finiteSynthesis_coordinateDerivative
#print axioms SingularClosure.finiteSynthesis_coordinateDerivative

example : ∀ (N : ℕ) (A : Fin 6)
    (a : FourierCoeff) (j : Fin 3),
    coordinateDerivative (physicalChannel N A a) j =
      physicalChannel N A (spectralMultiplier (derivativeSymbol j) a) :=
  @SingularClosure.physicalChannel_coordinateDerivative

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.physicalChannel_coordinateDerivative"
#check @SingularClosure.physicalChannel_coordinateDerivative
#print axioms SingularClosure.physicalChannel_coordinateDerivative

example : ∀ (N : ℕ) (A : Fin 6) (a : FourierCoeff),
    SpatialPeriodic (physicalChannel N A a) :=
  @SingularClosure.physicalChannel_periodic

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.physicalChannel_periodic"
#check @SingularClosure.physicalChannel_periodic
#print axioms SingularClosure.physicalChannel_periodic

example : ∀ (N : ℕ) (A : Fin 6)
    (a : FourierCoeff) (ha : SpectralSolenoidal a) (x : Vec),
    divergence (physicalChannel N A a) x = 0 :=
  @SingularClosure.physicalChannel_divergence_free

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.physicalChannel_divergence_free"
#check @SingularClosure.physicalChannel_divergence_free
#print axioms SingularClosure.physicalChannel_divergence_free

example : ∀ {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) (A : Fin 6) (x : Vec),
    divergence (physicalChannel N A (g.coeff t)) x = 0 :=
  @SingularClosure.GalerkinSolution.physicalChannel_divergence_free

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.physicalChannel_divergence_free"
#check @SingularClosure.GalerkinSolution.physicalChannel_divergence_free
#print axioms SingularClosure.GalerkinSolution.physicalChannel_divergence_free

example : ∀ {v : Field} (hv : ContDiff ℝ ∞ v),
    physicalEnstrophy v < ⊤ :=
  @SingularClosure.physicalEnstrophy_lt_top

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.physicalEnstrophy_lt_top"
#check @SingularClosure.physicalEnstrophy_lt_top
#print axioms SingularClosure.physicalEnstrophy_lt_top

example : ∀ (N : ℕ) (A B : Fin 6)
    (hA : A = 0 ∨ A = 1) (hB : B = 2 ∨ B = 3)
    (a b : FourierCoeff) (i j : Fin 3) (x : Vec),
    coordinateDerivative (physicalChannel N A a) i x j *
      coordinateDerivative (physicalChannel N B b) i x j = 0 :=
  @SingularClosure.physicalChannel_v_w_gradient_product_zero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.physicalChannel_v_w_gradient_product_zero"
#check @SingularClosure.physicalChannel_v_w_gradient_product_zero
#print axioms SingularClosure.physicalChannel_v_w_gradient_product_zero

example : ∀ (N : ℕ) (A B : Fin 6)
    (hA : A = 0 ∨ A = 1) (hB : B = 2 ∨ B = 3)
    (a b : FourierCoeff),
    physicalEnstrophy (physicalChannel N A a + physicalChannel N B b) =
      physicalEnstrophy (physicalChannel N A a) +
        physicalEnstrophy (physicalChannel N B b) :=
  @SingularClosure.PHYSICAL_V_W_ENSTROPHY_EQ

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.PHYSICAL_V_W_ENSTROPHY_EQ"
#check @SingularClosure.PHYSICAL_V_W_ENSTROPHY_EQ
#print axioms SingularClosure.PHYSICAL_V_W_ENSTROPHY_EQ

example : ∀ (ν : ℝ) (N : ℕ)
    (z₀ : FiniteGalerkinState N) (t₀ : ℝ),
    ∃ z : ℝ → FiniteGalerkinState N, z t₀ = z₀ ∧
      ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z (finiteGalerkinRhs ν N (z t)) t :=
  @SingularClosure.finiteGalerkinRhs_local_exists

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.finiteGalerkinRhs_local_exists"
#check @SingularClosure.finiteGalerkinRhs_local_exists
#print axioms SingularClosure.finiteGalerkinRhs_local_exists

example : ∀ (ν : ℝ) (N : ℕ) (R : ℝ),
    ∃ δ > (0 : ℝ),
      ∀ z₀ ∈ closedBall (0 : FiniteGalerkinState N) R, ∀ t₀ : ℝ,
        ∃ z : ℝ → FiniteGalerkinState N, z t₀ = z₀ ∧
          ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
            HasDerivAt z (finiteGalerkinRhs ν N (z t)) t :=
  @SingularClosure.finiteGalerkinRhs_uniform_local_time

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.finiteGalerkinRhs_uniform_local_time"
#check @SingularClosure.finiteGalerkinRhs_uniform_local_time
#print axioms SingularClosure.finiteGalerkinRhs_uniform_local_time

example : ∀ {ν : ℝ} {a : Field} {N : ℕ}
    (g h : GalerkinSolution ν a N),
    EqOn g.coeff h.coeff (Ici 0) :=
  @SingularClosure.GalerkinSolution.coeff_unique_forward

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coeff_unique_forward"
#check @SingularClosure.GalerkinSolution.coeff_unique_forward
#print axioms SingularClosure.GalerkinSolution.coeff_unique_forward

example : ∀ {ν : ℝ} {a : Field} {N : ℕ}
    (g h : GalerkinSolution ν a N),
    EqOn g.velocity h.velocity (Ici 0) :=
  @SingularClosure.GalerkinSolution.velocity_unique_forward

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.velocity_unique_forward"
#check @SingularClosure.GalerkinSolution.velocity_unique_forward
#print axioms SingularClosure.GalerkinSolution.velocity_unique_forward

example : ∀ (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0),
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      star (c k i) * coefficientTransport N c k i) = 0 :=
  @SingularClosure.coefficientTransport_complex_energy_zero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coefficientTransport_complex_energy_zero"
#check @SingularClosure.coefficientTransport_complex_energy_zero
#print axioms SingularClosure.coefficientTransport_complex_energy_zero

example : ∀ (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0),
    coefficientNonlinearPower N c = 0 :=
  @SingularClosure.coefficientNonlinearPower_eq_zero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coefficientNonlinearPower_eq_zero"
#check @SingularClosure.coefficientNonlinearPower_eq_zero
#print axioms SingularClosure.coefficientNonlinearPower_eq_zero

example : ∀ {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t),
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      ((-2 * ν) * coefficientDissipation N (g.coeff t)) (Ici 0) t :=
  @SingularClosure.GalerkinSolution.coefficientEnergy_identity

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientEnergy_identity"
#check @SingularClosure.GalerkinSolution.coefficientEnergy_identity
#print axioms SingularClosure.GalerkinSolution.coefficientEnergy_identity

example : ∀ {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t),
    coefficientEnergy N (g.coeff t) ≤ coefficientEnergy N (g.coeff 0) :=
  @SingularClosure.GalerkinSolution.coefficientEnergy_le_initial

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientEnergy_le_initial"
#check @SingularClosure.GalerkinSolution.coefficientEnergy_le_initial
#print axioms SingularClosure.GalerkinSolution.coefficientEnergy_le_initial

example : ∀ {ι : Type*} {y z d : ι → ℝ → ℝ} {ν κ T M E₀ : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hE₀ : 0 ≤ E₀)
    (hy : ∀ n, ContinuousOn (y n) (Icc 0 T))
    (hz : ∀ n, ContinuousOn (z n) (Icc 0 T))
    (hd : ∀ n, ContinuousOn (d n) (Icc 0 T))
    (hy_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ y n t)
    (h_initial : ∀ n, y n 0 ≤ E₀)
    (hderiv : ∀ n t, t ∈ Ioo 0 T → HasDerivAt (y n) (d n t) t)
    (hcubic : ∀ n t, t ∈ Ioo 0 T →
      d n t + ν * (z n t) ^ 2 ≤ κ * (y n t) ^ 3)
    (hbudget : ∀ n, (∫ s in (0 : ℝ)..T, (y n s) ^ 2) ≤ M),
    ∃ B : ℝ, 0 ≤ B ∧ B = E₀ * Real.exp (κ * M) ∧
      ∀ n,
        (∀ t ∈ Icc 0 T,
          y n t + ν * (∫ s in (0 : ℝ)..t, (z n s) ^ 2) ≤ B) ∧
        (∀ t ∈ Icc 0 T, y n t ≤ B) ∧
        ν * (∫ s in (0 : ℝ)..T, (z n s) ^ 2) ≤ B :=
  @SingularClosure.uniform_cubic_energy_of_square_budget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.uniform_cubic_energy_of_square_budget"
#check @SingularClosure.uniform_cubic_energy_of_square_budget
#print axioms SingularClosure.uniform_cubic_energy_of_square_budget

example : ∀ (k : Frequency) (v : Fin 3 → ℂ),
    (∑ i : Fin 3, (k i : ℂ) * coefficientLeray k v i) = 0 :=
  @SingularClosure.coefficientLeray_solenoidal

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coefficientLeray_solenoidal"
#check @SingularClosure.coefficientLeray_solenoidal
#print axioms SingularClosure.coefficientLeray_solenoidal

example : ∀ (ν : ℝ) (N : ℕ) (c : FourierCoeff)
    (hc : SpectralSolenoidal c) (k : Frequency),
    (∑ i : Fin 3, (k i : ℂ) * galerkinRhs ν N c k i) = 0 :=
  @SingularClosure.galerkinRhs_solenoidal

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.galerkinRhs_solenoidal"
#check @SingularClosure.galerkinRhs_solenoidal
#print axioms SingularClosure.galerkinRhs_solenoidal

example : ∀ (k : Frequency) (v : Fin 3 → ℂ)
    (i : Fin 3),
    v i + (((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k i : ℂ)) *
      pressureFromTransport k v = coefficientLeray k v i :=
  @SingularClosure.pressureFromTransport_recovery

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.pressureFromTransport_recovery"
#check @SingularClosure.pressureFromTransport_recovery
#print axioms SingularClosure.pressureFromTransport_recovery


open Metric

example : ∀ (N : ℕ) (a : FourierCoeff),
    physicalEnstrophy (finiteSynthesis N a) ≤ 6 * sixEnstrophy N a :=
  @SingularClosure.PHYSICAL_ENSTROPHY_LE_SIX_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.PHYSICAL_ENSTROPHY_LE_SIX_BUDGET"
#check @SingularClosure.PHYSICAL_ENSTROPHY_LE_SIX_BUDGET
#print axioms SingularClosure.PHYSICAL_ENSTROPHY_LE_SIX_BUDGET

example : ∀ (N : ℕ)
    (c : ℝ → FourierCoeff) (T : ℝ),
    (∫⁻ t in Icc (0 : ℝ) T,
      (physicalEnstrophy (finiteSynthesis N (c t))) ^ 2) ≤
        36 * budget6 N c T :=
  @SingularClosure.PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET"
#check @SingularClosure.PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET
#print axioms SingularClosure.PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET


open Metric

example : ∀ (k l : Frequency),
    (∫ x in unitCube, star (fourierCharacter k x) * fourierCharacter l x) =
      if k = l then 1 else 0 :=
  @SingularClosure.INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY"
#check @SingularClosure.INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY
#print axioms SingularClosure.INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY


open Metric

example : ∀ {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t),
    HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r))
      ((-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
        2 * coefficientEnstrophyNonlinearPower N (g.coeff t)) (Ici 0) t :=
  @SingularClosure.GalerkinSolution.coefficientEnstrophy_identity

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientEnstrophy_identity"
#check @SingularClosure.GalerkinSolution.coefficientEnstrophy_identity
#print axioms SingularClosure.GalerkinSolution.coefficientEnstrophy_identity

example : ∀ (N : ℕ) (c : FourierCoeff) (hc : SpectralSolenoidal c),
    coefficientEnstrophyNonlinearPower N c =
      ∑ k ∈ cutoffModes N,
        ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
          (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re :=
  @SingularClosure.coefficientEnstrophyNonlinearPower_eq_transport

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coefficientEnstrophyNonlinearPower_eq_transport"
#check @SingularClosure.coefficientEnstrophyNonlinearPower_eq_transport
#print axioms SingularClosure.coefficientEnstrophyNonlinearPower_eq_transport


example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (g : V → V) (hg : ContDiff ℝ 1 g)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ)) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (g (c t)) t :=
  SingularClosure.forwardGlobalSolution_exists g hg hdiss x₀

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.forwardGlobalSolution_exists"
#check @SingularClosure.forwardGlobalSolution_exists
#print axioms SingularClosure.forwardGlobalSolution_exists


open Metric

example : ∀ (ν : ℝ) (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c),
    SpectralReality (galerkinRhs ν N c) :=
  @SingularClosure.galerkinRhs_reality

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.galerkinRhs_reality"
#check @SingularClosure.galerkinRhs_reality
#print axioms SingularClosure.galerkinRhs_reality

example : ∀ {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T),
    coefficientEnergy N (g.coeff T) +
      2 * ν * (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t)) =
        coefficientEnergy N (g.coeff 0) :=
  @SingularClosure.GalerkinSolution.coefficientEnergy_integral_identity

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientEnergy_integral_identity"
#check @SingularClosure.GalerkinSolution.coefficientEnergy_integral_identity
#print axioms SingularClosure.GalerkinSolution.coefficientEnergy_integral_identity

example : ∀ {ν : ℝ} (hν : 0 < ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {T : ℝ} (hT : 0 ≤ T),
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t)) ≤
      coefficientEnergy N (datumFourierCoeff a) / (2 * ν) :=
  @SingularClosure.GalerkinSolution.coefficientDissipation_integral_le

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.coefficientDissipation_integral_le"
#check @SingularClosure.GalerkinSolution.coefficientDissipation_integral_le
#print axioms SingularClosure.GalerkinSolution.coefficientDissipation_integral_le

example : ∀ (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ)
    (z₀ : InvariantGalerkinState N),
    ∃ z : ℝ → InvariantGalerkinState N, z 0 = z₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt z (invariantGalerkinRhs ν N (z t)) t :=
  @SingularClosure.invariantGalerkinRhs_global_exists

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.invariantGalerkinRhs_global_exists"
#check @SingularClosure.invariantGalerkinRhs_global_exists
#print axioms SingularClosure.invariantGalerkinRhs_global_exists

example : ∀ (ν : ℝ) (hν : 0 ≤ ν)
    (a : Field) (N : ℕ)
    (hint : ∀ k : Frequency, ∀ i : Fin 3,
      MeasureTheory.IntegrableOn (datumFourierIntegrand a k i) unitCube MeasureTheory.volume)
    (hreal : SpectralReality (datumFourierCoeff a))
    (hsol : SpectralSolenoidal (datumFourierCoeff a)),
    Nonempty (GalerkinSolution ν a N) :=
  @SingularClosure.galerkinSolution_exists_of_fourier_invariants

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.galerkinSolution_exists_of_fourier_invariants"
#check @SingularClosure.galerkinSolution_exists_of_fourier_invariants
#print axioms SingularClosure.galerkinSolution_exists_of_fourier_invariants

example : ∀ (u : TorusVectorL2),
    (∑ A : Fin 6, torusL2Channel A u) = u :=
  @SingularClosure.TORUS_L2_SIX_CHANNEL_RECONSTRUCTION

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.TORUS_L2_SIX_CHANNEL_RECONSTRUCTION"
#check @SingularClosure.TORUS_L2_SIX_CHANNEL_RECONSTRUCTION
#print axioms SingularClosure.TORUS_L2_SIX_CHANNEL_RECONSTRUCTION

example : ∀ (A B : Fin 6) (hAB : A ≠ B)
    (u v : TorusVectorL2),
    inner ℂ (torusL2Channel A u) (torusL2Channel B v) = 0 :=
  @SingularClosure.TORUS_L2_SIX_CHANNEL_ORTHOGONAL

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.TORUS_L2_SIX_CHANNEL_ORTHOGONAL"
#check @SingularClosure.TORUS_L2_SIX_CHANNEL_ORTHOGONAL
#print axioms SingularClosure.TORUS_L2_SIX_CHANNEL_ORTHOGONAL

example : ∀ (u : TorusVectorL2),
    ‖u‖ ^ 2 = ∑ A : Fin 6, ‖torusL2Channel A u‖ ^ 2 :=
  @SingularClosure.TORUS_L2_SIX_CHANNEL_PYTHAGORAS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.TORUS_L2_SIX_CHANNEL_PYTHAGORAS"
#check @SingularClosure.TORUS_L2_SIX_CHANNEL_PYTHAGORAS
#print axioms SingularClosure.TORUS_L2_SIX_CHANNEL_PYTHAGORAS

example : ∀ (A : Fin 6) (u : TorusVectorL2),
    torusVectorFourierCoeff (torusL2Channel A u) =
      spectralChannel A (torusVectorFourierCoeff u) :=
  @SingularClosure.torusL2Channel_fourierCoeff

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.torusL2Channel_fourierCoeff"
#check @SingularClosure.torusL2Channel_fourierCoeff
#print axioms SingularClosure.torusL2Channel_fourierCoeff

example : ∀ (A : Fin 6) (u : TorusVectorL2)
    (hu : ∀ i : Fin 3, (∫ x, u i x) = 0),
    ∀ i : Fin 3, (∫ x, torusL2Channel A u i x) = 0 :=
  @SingularClosure.torusL2Channel_preserves_mean

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.torusL2Channel_preserves_mean"
#check @SingularClosure.torusL2Channel_preserves_mean
#print axioms SingularClosure.torusL2Channel_preserves_mean

example : ∀ (N : ℕ) (A B : Fin 6)
    (hAB : A ≠ B) (a b : FourierCoeff) (i j : Fin 3),
    (∫ x in unitCube,
      coordinateDerivative (physicalChannel N A a) i x j *
      coordinateDerivative (physicalChannel N B b) i x j) = 0 :=
  @SingularClosure.PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY"
#check @SingularClosure.PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY
#print axioms SingularClosure.PHYSICAL_CHANNEL_GRADIENT_ORTHOGONALITY

example : ∀ (N : ℕ) (a : FourierCoeff),
    sixEnstrophy N a = physicalEnstrophy (finiteSynthesis N a) :=
  @SingularClosure.SIX_CHANNEL_FINITE_ENSTROPHY_EQ

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_FINITE_ENSTROPHY_EQ"
#check @SingularClosure.SIX_CHANNEL_FINITE_ENSTROPHY_EQ
#print axioms SingularClosure.SIX_CHANNEL_FINITE_ENSTROPHY_EQ

example : ∀ (N : ℕ)
    (c : ℝ → FourierCoeff) (T : ℝ),
    budget6 N c T = ∫⁻ t in Icc (0 : ℝ) T,
      (physicalEnstrophy (finiteSynthesis N (c t))) ^ 2 :=
  @SingularClosure.SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ"
#check @SingularClosure.SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ
#print axioms SingularClosure.SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ

example : ∀ (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T),
    ∃ M : ℝ≥0, ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫⁻ t in Icc (0 : ℝ) T, (physicalEnstrophy (g.velocity t)) ^ 2) ≤
        (M : ℝ≥0∞) :=
  @SingularClosure.ax6_physical_square_budget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.ax6_physical_square_budget"
#check @SingularClosure.ax6_physical_square_budget
#print axioms SingularClosure.ax6_physical_square_budget


open Metric

example : ∀ (j : Fin 3) (a : Field),
    coordinateAverage j (coordinateAverage j a) = coordinateAverage j a :=
  @SingularClosure.coordinateAverage_idempotent

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coordinateAverage_idempotent"
#check @SingularClosure.coordinateAverage_idempotent
#print axioms SingularClosure.coordinateAverage_idempotent

example : ∀ (j : Fin 3) (a : Field)
    (ha : SpatialPeriodic a),
    SpatialPeriodic (coordinateAverage j a) :=
  @SingularClosure.coordinateAverage_periodic

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coordinateAverage_periodic"
#check @SingularClosure.coordinateAverage_periodic
#print axioms SingularClosure.coordinateAverage_periodic

example : ∀ (j : Fin 3) (a : Field)
    (x : Vec),
    coordinateDerivative (coordinateAverage j a) j x = 0 :=
  @SingularClosure.coordinateAverage_own_coordinateDerivative_zero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.coordinateAverage_own_coordinateDerivative_zero"
#check @SingularClosure.coordinateAverage_own_coordinateDerivative_zero
#print axioms SingularClosure.coordinateAverage_own_coordinateDerivative_zero


open Metric

example : ∀ {a : Field}
    (ha : SmoothSigmaZero a) (k : Frequency) (i : Fin 3),
    IntegrableOn (datumFourierIntegrand a k i) unitCube volume :=
  @SingularClosure.smoothSigmaZero_fourier_integrable

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.smoothSigmaZero_fourier_integrable"
#check @SingularClosure.smoothSigmaZero_fourier_integrable
#print axioms SingularClosure.smoothSigmaZero_fourier_integrable

example : ∀ (a : Field),
    SpectralReality (datumFourierCoeff a) :=
  @SingularClosure.datumFourierCoeff_reality

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.datumFourierCoeff_reality"
#check @SingularClosure.datumFourierCoeff_reality
#print axioms SingularClosure.datumFourierCoeff_reality

example : ∀ {a : Field}
    (ha : SmoothSigmaZero a),
    SpectralSolenoidal (datumFourierCoeff a) :=
  @SingularClosure.smoothSigmaZero_fourier_solenoidal

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.smoothSigmaZero_fourier_solenoidal"
#check @SingularClosure.smoothSigmaZero_fourier_solenoidal
#print axioms SingularClosure.smoothSigmaZero_fourier_solenoidal

example : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : Field) (ha : SmoothSigmaZero a) (N : ℕ),
    ∃ g : GalerkinSolution ν a N, ∀ h : GalerkinSolution ν a N,
      EqOn g.coeff h.coeff (Ici 0) :=
  @SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE"
#check @SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE
#print axioms SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE

end
