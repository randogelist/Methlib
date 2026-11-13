import QFA.Endpoints.Agmon.Contracts
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NormNum

/-!
# QFA AD01: spatial real-to-complex representation

STATUS = A_TIER_CANDIDATE.
Source pin: Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, Lean 4.33.0.
No local Lean execution. Matching external compilation and theorem-level
axiom-audit evidence remain required.

The carriers are exactly Agmon.Space, Agmon.ComplexVector, and Agmon.ComplexL2.
The spatial measure is full Lebesgue volume; no finite-volume premise occurs.
EP001--EP006 are the stable point-of-use sources from D02.01--D02.03.

The module constructs a real linear vector isometry, its spatial L2 lift,
the a.e. representative identity, norm/energy preservation, and transport of
actual compact-real-test weak directional derivative identities. Test-integrand
integrability is derived before continuous-linear integral commutation.

AD08 remains separate: the real-test identities below are not Schwartz
distribution identities. No gradient or Laplacian witness is constructed for
an arbitrary field, and no QFA regularity or NSE conclusion is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped ContDiff

namespace QFA.Endpoints.Representation

open QFA.Endpoints.Agmon

noncomputable section

/-- Real spatial L2 on the same full-volume domain as Agmon.ComplexL2. -/
abbrev RealL2 := Lp Space 2 (volume : Measure Space)

/-- EP001 and EP002: componentwise complexification with the Euclidean norm.

The finite sum in EP002 compares the real and complex Euclidean norms directly;
no component-count factor is introduced.
-/
def complexifyVectorLI : Space →ₗᵢ[ℝ] ComplexVector where
  toFun v := WithLp.toLp 2 (fun j : Fin 3 => Complex.ofRealLI (v j))
  map_add' v w := by
    apply PiLp.ext
    intro j
    exact Complex.ofRealLI.map_add (v j) (w j)
  map_smul' c v := by
    apply PiLp.ext
    intro j
    exact Complex.ofRealLI.map_smul c (v j)
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    -- EP002: squared norms on both Euclidean vector spaces.
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    -- EP001: each real-coordinate embedding preserves its scalar norm.
    exact congrArg (fun t : ℝ => t ^ 2) (Complex.ofRealLI.norm_map (v j))

@[simp]
theorem complexifyVectorLI_apply (v : Space) (j : Fin 3) :
    complexifyVectorLI v j = (v j : ℂ) := rfl

@[simp]
theorem complexifyVectorLI_zero : complexifyVectorLI 0 = 0 :=
  complexifyVectorLI.map_zero

@[simp]
theorem complexifyVectorLI_norm (v : Space) : ‖complexifyVectorLI v‖ = ‖v‖ :=
  complexifyVectorLI.norm_map v

theorem complexifyVectorLI_norm_sq (v : Space) :
    ‖complexifyVectorLI v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [complexifyVectorLI_norm]

theorem complexifyVectorLI_isometry : Isometry complexifyVectorLI :=
  complexifyVectorLI.isometry

/-- The actual continuous real linear map used in the Bochner integral adapter. -/
def complexifyVectorCLM : Space →L[ℝ] ComplexVector :=
  complexifyVectorLI.toContinuousLinearMap

/-- EP003: lift the zero-preserving Lipschitz isometry to spatial L2. -/
def complexifyL2 (v : RealL2) : ComplexL2 :=
  complexifyVectorLI.isometry.lipschitz.compLp complexifyVectorLI.map_zero v

/-- EP004: equality of chosen representatives holds almost everywhere. -/
theorem complexifyL2_ae (v : RealL2) :
    (fun x : Space => complexifyL2 v x) =ᵐ[volume]
      (fun x : Space => complexifyVectorLI (v x)) :=
  complexifyVectorLI.isometry.lipschitz.coeFn_compLp complexifyVectorLI.map_zero v

/-- EP005 in both directions: preservation of the full-volume L2 norm. -/
@[simp]
theorem complexifyL2_norm (v : RealL2) : ‖complexifyL2 v‖ = ‖v‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [complexifyL2_ae v] with x hx
    exact ((congrArg norm hx).trans (complexifyVectorLI_norm (v x))).le
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [complexifyL2_ae v] with x hx
    exact ((congrArg norm hx).trans (complexifyVectorLI_norm (v x))).ge

theorem complexifyL2_add (v w : RealL2) :
    complexifyL2 (v + w) = complexifyL2 v + complexifyL2 w := by
  apply Lp.ext
  filter_upwards [complexifyL2_ae (v + w), complexifyL2_ae v, complexifyL2_ae w,
    Lp.coeFn_add v w, Lp.coeFn_add (complexifyL2 v) (complexifyL2 w)]
      with x hsum hv hw hadd hcomplexadd
  simp only [hsum, hadd, hcomplexadd, hv, hw, Pi.add_apply, map_add]

theorem complexifyL2_smul (c : ℝ) (v : RealL2) :
    complexifyL2 (c • v) = c • complexifyL2 v := by
  apply Lp.ext
  filter_upwards [complexifyL2_ae (c • v), complexifyL2_ae v,
    Lp.coeFn_smul c v, Lp.coeFn_smul c (complexifyL2 v)]
      with x hscaled hv hsmul hcomplexsmul
  simp only [hscaled, hsmul, hcomplexsmul, hv, Pi.smul_apply, map_smul]

/-- The induced actual real linear isometry of spatial L2 spaces. -/
def complexifyL2LI : RealL2 →ₗᵢ[ℝ] ComplexL2 where
  toFun := complexifyL2
  map_add' := complexifyL2_add
  map_smul' := complexifyL2_smul
  norm_map' := complexifyL2_norm

theorem complexifyL2_isometry : Isometry complexifyL2 :=
  complexifyL2LI.isometry

@[simp]
theorem complexifyL2_zero : complexifyL2 0 = 0 :=
  complexifyL2LI.map_zero

theorem complexifyL2_velocityEnergy (v : RealL2) :
    velocityEnergy (complexifyL2 v) = ‖v‖ ^ 2 := by
  unfold velocityEnergy
  rw [complexifyL2_norm]

/-- Frobenius gradient energy: the sum of the three directional squared norms. -/
theorem complexifyL2_gradientEnergy (G : Fin 3 → RealL2) :
    gradientEnergy (fun j => complexifyL2 (G j)) = ∑ j : Fin 3, ‖G j‖ ^ 2 := by
  unfold gradientEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [complexifyL2_norm]

/-- Norm preservation for a supplied L2 Laplacian witness; no witness is invented. -/
theorem complexifyL2_laplacianEnergy (L : RealL2) :
    laplacianEnergy (complexifyL2 L) = ‖L‖ ^ 2 := by
  unfold laplacianEnergy
  rw [complexifyL2_norm]

/-- Compact continuous test functions turn full-volume L2 fields into L1 products.

The premise `1 ≤ 2` and local finiteness of spatial volume permit
EP051 MemLp.locallyIntegrable; compact support then supplies actual integrability.
-/
theorem integrable_compact_test_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : Lp F 2 (volume : Measure Space)) {ψ : Space → ℝ}
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (fun x : Space => ψ x • v x) volume :=
  ((Lp.memLp v).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    hψ hcompact

/-- EP004 and EP006: real scalar test pairings commute with complexification.

Integrability of the real pairing is explicit. In the weak-derivative theorem
below it is discharged from compact support and L2 membership.
-/
theorem integral_test_smul_complexifyL2
    (v : RealL2) (ψ : Space → ℝ)
    (hInt : Integrable (fun x : Space => ψ x • v x) volume) :
    (∫ x : Space, ψ x • complexifyL2 v x) =
      complexifyVectorCLM (∫ x : Space, ψ x • v x) := by
  calc
    (∫ x : Space, ψ x • complexifyL2 v x) =
        ∫ x : Space, complexifyVectorCLM (ψ x • v x) := by
      apply integral_congr_ae
      filter_upwards [complexifyL2_ae v] with x hx
      rw [hx]
      exact (complexifyVectorLI.map_smul (ψ x) (v x)).symm
    _ = complexifyVectorCLM (∫ x : Space, ψ x • v x) :=
      -- EP006: both domain and codomain are complete real normed spaces.
      complexifyVectorCLM.integral_comp_comm hInt

/-- Transport an integrable weak-test equality, retaining its negative sign. -/
theorem weakTestIdentity_complexify
    (v G : RealL2) (dψ ψ : Space → ℝ)
    (hv : Integrable (fun x : Space => dψ x • v x) volume)
    (hG : Integrable (fun x : Space => ψ x • G x) volume)
    (hId : (∫ x : Space, dψ x • v x) = -(∫ x : Space, ψ x • G x)) :
    (∫ x : Space, dψ x • complexifyL2 v x) =
      -(∫ x : Space, ψ x • complexifyL2 G x) := by
  rw [integral_test_smul_complexifyL2 v dψ hv,
    integral_test_smul_complexifyL2 G ψ hG, hId]
  exact complexifyVectorCLM.map_neg _

/-- Actual weak directional differentiation against real compact smooth tests.

The same definition applies to real and complex vector-valued L2 fields.
It neither asserts existence of a derivative witness nor identifies a
Schwartz tempered-distribution derivative. That extension is AD08.
-/
def RealTestWeakDirectionalDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (v G : Lp F 2 (volume : Measure Space)) (e : Space) : Prop :=
  ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x : Space, (fderiv ℝ ψ x e) • v x) = -(∫ x : Space, ψ x • G x)

/-- D02.03: transport a physical compact-test weak directional derivative.

The derivative of a compact smooth scalar test remains compactly supported
and continuous. Thus both real pairings are integrable before EP006 is used.
Repeated application transports supplied higher directional-derivative chains.
-/
theorem complexifyL2_weakDirectionalDerivative
    {v G : RealL2} {e : Space} (h : RealTestWeakDirectionalDerivative v G e) :
    RealTestWeakDirectionalDerivative (complexifyL2 v) (complexifyL2 G) e := by
  intro ψ hψ hcompact
  have hDerivative : Integrable (fun x : Space => (fderiv ℝ ψ x e) • v x) volume :=
    integrable_compact_test_smul v
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcompact.fderiv_apply ℝ e)
  have hValue : Integrable (fun x : Space => ψ x • G x) volume :=
    integrable_compact_test_smul G hψ.continuous hcompact
  exact weakTestIdentity_complexify v G (fun x => fderiv ℝ ψ x e) ψ
    hDerivative hValue (h ψ hψ hcompact)

end

end QFA.Endpoints.Representation
