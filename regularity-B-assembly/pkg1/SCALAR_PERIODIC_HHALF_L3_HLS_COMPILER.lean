import PERIODIC_HHALF_L3_COMPONENT_COMPILER

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace ScalarPeriodicHhalfL3HLSCompiler

open H12CriticalTrilinearCompiler
open NSEPhysicalLpDataConstruction
open PeriodicStrongSliceToRawPhysicalFields
open PeriodicHhalfL3ComponentCompiler

/-- The physical unit three-torus. -/
abbrev Torus3 := UnitAddTorus (Fin 3)

/-- Normed-space side condition for the `L²` source space. -/
instance factTwo : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

/--
A bounded periodic Riesz-half operator certificate.

The intended operator is the mean-zero inverse fractional derivative

  `Λ⁻¹ᐟ² : L²₀(T³) → L³(T³)`.

The analytic HLS theorem is exactly the construction of such an operator,
its norm bound, and the reconstruction identities used below.
-/
structure PeriodicRieszHalfCertificate where
  Cscalar : ℝ
  Cscalar_pos : 0 < Cscalar
  operator :
    Lp ℝ 2 (volume : Measure Torus3) →L[ℝ]
      Lp ℝ 3 (volume : Measure Torus3)
  operator_norm_le :
    ‖operator‖ ≤ Cscalar

/--
One scalar reconstruction through the certified periodic Riesz-half
operator.
-/
structure ScalarReconstruction
    (H : PeriodicRieszHalfCertificate) where
  halfDerivative :
    Lp ℝ 2 (volume : Measure Torus3)
  field :
    Lp ℝ 3 (volume : Measure Torus3)
  reconstruction :
    field = H.operator halfDerivative

/--
The bounded operator certificate gives the scalar periodic
`H^(1/2) → L³` estimate for every reconstructed field.
-/
theorem scalar_l3_le
    (H : PeriodicRieszHalfCertificate)
    (f : ScalarReconstruction H) :
    ‖f.field‖ ≤
      H.Cscalar * ‖f.halfDerivative‖ := by
  rw [f.reconstruction]
  calc
    ‖H.operator f.halfDerivative‖
        ≤ ‖H.operator‖ * ‖f.halfDerivative‖ :=
      H.operator.le_opNorm f.halfDerivative
    _ ≤ H.Cscalar * ‖f.halfDerivative‖ :=
      mul_le_mul_of_nonneg_right
        H.operator_norm_le
        (norm_nonneg f.halfDerivative)

/--
Component realizations of one critical state through the same scalar
periodic Riesz-half operator.

The decomposition inequalities contain only finite-dimensional norm
aggregation.  All analytic scalar bounds are derived from `H.operator`.
-/
structure HLSComponentData
    (s : CriticalState)
    (H : PeriodicRieszHalfCertificate) where
  velocity :
    Fin 3 → ScalarReconstruction H
  gradient :
    Fin 3 → Fin 3 → ScalarReconstruction H
  lambda :
    Fin 3 → ScalarReconstruction H
  velocityDecompose :
    s.U3 ≤
      sum3 (fun i => ‖(velocity i).field‖)
  gradientDecompose :
    s.G3 ≤
      sum9 (fun i j => ‖(gradient i j).field‖)
  lambdaDecompose :
    s.L3 ≤
      sum3 (fun i => ‖(lambda i).field‖)
  velocityHalfBound :
    ∀ i, ‖(velocity i).halfDerivative‖ ≤ s.E
  gradientHalfBound :
    ∀ i j, ‖(gradient i j).halfDerivative‖ ≤ s.D
  lambdaHalfBound :
    ∀ i, ‖(lambda i).halfDerivative‖ ≤ s.D

theorem velocity_component_bound
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H)
    (i : Fin 3) :
    ‖(D.velocity i).field‖ ≤
      H.Cscalar * s.E := by
  calc
    ‖(D.velocity i).field‖
        ≤ H.Cscalar *
            ‖(D.velocity i).halfDerivative‖ :=
      scalar_l3_le H (D.velocity i)
    _ ≤ H.Cscalar * s.E :=
      mul_le_mul_of_nonneg_left
        (D.velocityHalfBound i)
        H.Cscalar_pos.le

theorem gradient_component_bound
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H)
    (i j : Fin 3) :
    ‖(D.gradient i j).field‖ ≤
      H.Cscalar * s.D := by
  calc
    ‖(D.gradient i j).field‖
        ≤ H.Cscalar *
            ‖(D.gradient i j).halfDerivative‖ :=
      scalar_l3_le H (D.gradient i j)
    _ ≤ H.Cscalar * s.D :=
      mul_le_mul_of_nonneg_left
        (D.gradientHalfBound i j)
        H.Cscalar_pos.le

theorem lambda_component_bound
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H)
    (i : Fin 3) :
    ‖(D.lambda i).field‖ ≤
      H.Cscalar * s.D := by
  calc
    ‖(D.lambda i).field‖
        ≤ H.Cscalar *
            ‖(D.lambda i).halfDerivative‖ :=
      scalar_l3_le H (D.lambda i)
    _ ≤ H.Cscalar * s.D :=
      mul_le_mul_of_nonneg_left
        (D.lambdaHalfBound i)
        H.Cscalar_pos.le

/--
Compile the periodic HLS operator data into the exact scalar component
certificate consumed by the already A-tier vector/matrix compiler.
-/
def toScalarEndpointCertificate
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H) :
    ScalarEndpointCertificate s where
  Cscalar := H.Cscalar
  Cscalar_pos := H.Cscalar_pos
  velocityComponent :=
    fun i => ‖(D.velocity i).field‖
  gradientComponent :=
    fun i j => ‖(D.gradient i j).field‖
  lambdaComponent :=
    fun i => ‖(D.lambda i).field‖
  velocityDecompose := D.velocityDecompose
  gradientDecompose := D.gradientDecompose
  lambdaDecompose := D.lambdaDecompose
  velocityComponentBound :=
    velocity_component_bound H D
  gradientComponentBound :=
    gradient_component_bound H D
  lambdaComponentBound :=
    lambda_component_bound H D

/--
Compile the periodic HLS certificate directly to the exact
`PeriodicHhalfL3` data structure.
-/
def compilePeriodicHhalfL3
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H) :
    PeriodicHhalfL3 s :=
  PeriodicHhalfL3ComponentCompiler.toPeriodicHhalfL3
    (toScalarEndpointCertificate H D)

/--
The compiled common constant is exactly `9 * Cscalar`.
-/
theorem compiled_C3_eq
    {s : CriticalState}
    (H : PeriodicRieszHalfCertificate)
    (D : HLSComponentData s H) :
    (compilePeriodicHhalfL3 H D).C3 =
      9 * H.Cscalar := by
  rfl

/--
Composition with the complete periodic strong-slice nonlinear chain.
-/
theorem critical_trilinear_of_hls
    (S : PeriodicStrongSlice)
    (E Dnorm : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ Dnorm)
    (H : PeriodicRieszHalfCertificate)
    (R :
      HLSComponentData
        (physicalState
          (toRawPhysicalFields S)
          E Dnorm hE hD)
        H) :
    (physicalState
      (toRawPhysicalFields S)
      E Dnorm hE hD).Iabs
      ≤ criticalConstant
          (compilePeriodicHhalfL3 H R)
          * E * Dnorm ^ 2 := by
  exact critical_trilinear_of_periodicStrongSlice
    S E Dnorm hE hD
    (compilePeriodicHhalfL3 H R)

/--
Composition with the already A-tier viscosity-absorption radius.
-/
theorem critical_trilinear_absorbed_of_hls
    {ν : ℝ}
    (hν : 0 < ν)
    (S : PeriodicStrongSlice)
    (E Dnorm : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ Dnorm)
    (H : PeriodicRieszHalfCertificate)
    (R :
      HLSComponentData
        (physicalState
          (toRawPhysicalFields S)
          E Dnorm hE hD)
        H)
    (hsmall :
      E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant
          (compilePeriodicHhalfL3 H R))) :
    (physicalState
      (toRawPhysicalFields S)
      E Dnorm hE hD).Iabs
      ≤ (ν / 4) * Dnorm ^ 2 := by
  exact critical_trilinear_absorbed_of_periodicStrongSlice
    hν S E Dnorm hE hD
    (compilePeriodicHhalfL3 H R)
    hsmall

/--
Proposition-valued audited root.

A bounded periodic Riesz-half certificate and component reconstructions
produce an exact `PeriodicHhalfL3` witness with constant `9 * Cscalar`.
-/
theorem SCALAR_PERIODIC_HHALF_L3_HLS_COMPILER :
    ∀ {s : CriticalState}
      (H : PeriodicRieszHalfCertificate)
      (D : HLSComponentData s H),
      ∃ hS : PeriodicHhalfL3 s,
        hS.C3 = 9 * H.Cscalar := by
  intro s H D
  exact ⟨compilePeriodicHhalfL3 H D,
    compiled_C3_eq H D⟩

end ScalarPeriodicHhalfL3HLSCompiler
