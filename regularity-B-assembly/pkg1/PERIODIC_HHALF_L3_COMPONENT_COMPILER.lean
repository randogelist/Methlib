import PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS

set_option autoImplicit false

noncomputable section

namespace PeriodicHhalfL3ComponentCompiler

open H12CriticalTrilinearCompiler
open NSEPhysicalLpDataConstruction
open PeriodicStrongSliceToRawPhysicalFields

/-- Explicit sum of three scalar components. -/
def sum3 (a : Fin 3 → ℝ) : ℝ :=
  a 0 + a 1 + a 2

/-- Explicit sum of the nine entries of a three-by-three field. -/
def sum9 (a : Fin 3 → Fin 3 → ℝ) : ℝ :=
  sum3 (fun i => sum3 (a i))

theorem sum3_le_of_forall_le
    (a : Fin 3 → ℝ) (M : ℝ)
    (h : ∀ i, a i ≤ M) :
    sum3 a ≤ 3 * M := by
  unfold sum3
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  nlinarith

theorem sum9_le_of_forall_le
    (a : Fin 3 → Fin 3 → ℝ) (M : ℝ)
    (h : ∀ i j, a i j ≤ M) :
    sum9 a ≤ 9 * M := by
  have hrow :
      ∀ i, sum3 (a i) ≤ 3 * M := by
    intro i
    exact sum3_le_of_forall_le (a i) M (h i)
  have hout :=
    sum3_le_of_forall_le
      (fun i => sum3 (a i))
      (3 * M)
      hrow
  change sum3 (fun i => sum3 (a i)) ≤ 9 * M
  nlinarith

/--
Componentwise scalar periodic Sobolev certificate.

For an actual vector field, the intended components are:

* `velocityComponent i = ||u_i||_L3`;
* `gradientComponent i j = ||∂_j u_i||_L3`;
* `lambdaComponent i = ||(Λu)_i||_L3`.

The component bounds are exactly the scalar
`H^(1/2)(T^3) -> L^3(T^3)` endpoint after the corresponding spectral
component norm is dominated by `E` or `D`.
-/
structure ScalarEndpointCertificate
    (s : CriticalState) where
  Cscalar : ℝ
  Cscalar_pos : 0 < Cscalar
  velocityComponent : Fin 3 → ℝ
  gradientComponent : Fin 3 → Fin 3 → ℝ
  lambdaComponent : Fin 3 → ℝ
  velocityDecompose :
    s.U3 ≤ sum3 velocityComponent
  gradientDecompose :
    s.G3 ≤ sum9 gradientComponent
  lambdaDecompose :
    s.L3 ≤ sum3 lambdaComponent
  velocityComponentBound :
    ∀ i, velocityComponent i ≤ Cscalar * s.E
  gradientComponentBound :
    ∀ i j, gradientComponent i j ≤ Cscalar * s.D
  lambdaComponentBound :
    ∀ i, lambdaComponent i ≤ Cscalar * s.D

/--
Safe common vector/matrix constant.

Nine scalar gradient entries dominate the three velocity and three
fractional-derivative components, so `9*Cscalar` controls all endpoints.
-/
def compiledConstant
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) : ℝ :=
  9 * h.Cscalar

theorem compiledConstant_pos
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) :
    0 < compiledConstant h := by
  unfold compiledConstant
  nlinarith [h.Cscalar_pos]

theorem velocity_compiled
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) :
    s.U3 ≤ compiledConstant h * s.E := by
  have hsum :
      sum3 h.velocityComponent
        ≤ 3 * (h.Cscalar * s.E) :=
    sum3_le_of_forall_le
      h.velocityComponent
      (h.Cscalar * s.E)
      h.velocityComponentBound
  have hbase := h.velocityDecompose.trans hsum
  unfold compiledConstant
  have hCE : 0 ≤ h.Cscalar * s.E :=
    mul_nonneg h.Cscalar_pos.le s.E_nonneg
  nlinarith

theorem gradient_compiled
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) :
    s.G3 ≤ compiledConstant h * s.D := by
  have hsum :
      sum9 h.gradientComponent
        ≤ 9 * (h.Cscalar * s.D) :=
    sum9_le_of_forall_le
      h.gradientComponent
      (h.Cscalar * s.D)
      h.gradientComponentBound
  have hbase := h.gradientDecompose.trans hsum
  unfold compiledConstant
  nlinarith

theorem lambda_compiled
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) :
    s.L3 ≤ compiledConstant h * s.D := by
  have hsum :
      sum3 h.lambdaComponent
        ≤ 3 * (h.Cscalar * s.D) :=
    sum3_le_of_forall_le
      h.lambdaComponent
      (h.Cscalar * s.D)
      h.lambdaComponentBound
  have hbase := h.lambdaDecompose.trans hsum
  unfold compiledConstant
  have hCD : 0 ≤ h.Cscalar * s.D :=
    mul_nonneg h.Cscalar_pos.le s.D_nonneg
  nlinarith

/--
The scalar component endpoint compiles to the exact
`PeriodicHhalfL3` structure consumed by the critical trilinear chain.
-/
def toPeriodicHhalfL3
    {s : CriticalState}
    (h : ScalarEndpointCertificate s) :
    PeriodicHhalfL3 s where
  C3 := compiledConstant h
  C3_pos := compiledConstant_pos h
  velocity := velocity_compiled h
  gradient := gradient_compiled h
  lambda := lambda_compiled h

/--
Composition with the complete periodic strong-slice semantic chain.
-/
theorem critical_trilinear_of_scalarEndpoint
    (S : PeriodicStrongSlice)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (h :
      ScalarEndpointCertificate
        (physicalState
          (toRawPhysicalFields S)
          E D hE hD)) :
    (physicalState
      (toRawPhysicalFields S)
      E D hE hD).Iabs
      ≤ criticalConstant (toPeriodicHhalfL3 h) * E * D ^ 2 := by
  exact critical_trilinear_of_periodicStrongSlice
    S E D hE hD
    (toPeriodicHhalfL3 h)

/--
Composition with the already A-tier viscosity-absorption radius.
-/
theorem critical_trilinear_absorbed_of_scalarEndpoint
    {ν : ℝ}
    (hν : 0 < ν)
    (S : PeriodicStrongSlice)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (h :
      ScalarEndpointCertificate
        (physicalState
          (toRawPhysicalFields S)
          E D hE hD))
    (hsmall :
      E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant (toPeriodicHhalfL3 h))) :
    (physicalState
      (toRawPhysicalFields S)
      E D hE hD).Iabs
      ≤ (ν / 4) * D ^ 2 := by
  exact critical_trilinear_absorbed_of_periodicStrongSlice
    hν S E D hE hD
    (toPeriodicHhalfL3 h)
    hsmall

/--
Proposition-valued audited root.

The exact data compiler is `toPeriodicHhalfL3`.  This theorem records that
the componentwise scalar endpoint produces a `PeriodicHhalfL3` witness with
the exact compiled constant `9 * Cscalar`.
-/
theorem PERIODIC_HHALF_L3_COMPONENT_COMPILER :
    ∀ {s : CriticalState}
      (h : ScalarEndpointCertificate s),
      ∃ hS : PeriodicHhalfL3 s,
        hS.C3 = compiledConstant h := by
  intro s h
  exact ⟨toPeriodicHhalfL3 h, rfl⟩

end PeriodicHhalfL3ComponentCompiler
