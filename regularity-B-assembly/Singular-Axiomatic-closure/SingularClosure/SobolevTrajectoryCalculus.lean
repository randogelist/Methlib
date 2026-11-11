import SingularClosure.TorusGalerkinSobolev
import SingularClosure.GalerkinExistence
import SingularClosure.GalerkinTimeDerivative

/-!
# Actual Galerkin trajectories as Bochner-Sobolev paths

The finite state is embedded by its literal zero-extended Fourier coefficients.
Finite-dimensional automatic continuity supplies the continuous linear map;
all path continuity, derivatives, and finite-time Lp membership follow from
the actual Galerkin equation.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SingularClosure

noncomputable section

instance torusSobolevNormedSpaceReal (s : ℕ) : NormedSpace ℝ (TorusSobolev s) :=
  NormedSpace.restrictScalars ℝ ℂ (TorusSobolev s)

instance torusSobolevRealScalarTower (s : ℕ) : IsScalarTower ℝ ℂ (TorusSobolev s) :=
  Real.isScalarTower

def finiteStateSobolevComplexLinear (s N : ℕ) :
    FiniteGalerkinState N →ₗ[ℂ] TorusSobolev s where
  toFun z := finiteSobolev s N (extendFiniteState N z)
  map_add' z w := by
    apply Subtype.ext
    change cutoffCoeff N (extendFiniteState N (z + w)) =
      cutoffCoeff N (extendFiniteState N z) + cutoffCoeff N (extendFiniteState N w)
    funext k i
    by_cases hk : k ∈ cutoffModes N <;>
      simp [cutoffCoeff, extendFiniteState, hk]
  map_smul' r z := by
    apply Subtype.ext
    change cutoffCoeff N (extendFiniteState N (r • z)) =
      r • cutoffCoeff N (extendFiniteState N z)
    funext k i
    by_cases hk : k ∈ cutoffModes N <;>
      simp [cutoffCoeff, extendFiniteState, hk]

/-- The finite coefficient state as a genuine vector in the weighted Sobolev Hilbert space. -/
def finiteStateSobolev (s N : ℕ) : FiniteGalerkinState N →L[ℝ] TorusSobolev s :=
  ((finiteStateSobolevComplexLinear s N).restrictScalars ℝ).toContinuousLinearMap

theorem finiteStateSobolev_apply (s N : ℕ) (z : FiniteGalerkinState N) :
    finiteStateSobolev s N z = finiteSobolev s N (extendFiniteState N z) := rfl

theorem finiteStateSobolev_restrict (s N : ℕ) (c : FourierCoeff) :
    finiteStateSobolev s N (restrictFiniteState N c) = finiteSobolev s N c := by
  rw [finiteStateSobolev_apply]
  apply Subtype.ext
  change cutoffCoeff N (extendFiniteState N (restrictFiniteState N c)) = cutoffCoeff N c
  rw [extend_restrictFiniteState, cutoffCoeff_idempotent]

theorem GalerkinSolution.sobolevState_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (s : ℕ) :
    ContinuousOn (g.sobolevState s) (Ici 0) := by
  have h := (finiteStateSobolev s N).continuous.comp_continuousOn g.finite_continuousOn
  simpa only [Function.comp_def, finiteStateSobolev_restrict,
    GalerkinSolution.sobolevState] using! h

/-- The literal finite Galerkin vector field represented in the Sobolev space. -/
def GalerkinSolution.rhsSobolev {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (s : ℕ) (t : ℝ) : TorusSobolev s :=
  finiteStateSobolev s N (finiteGalerkinRhs ν N (restrictFiniteState N (g.coeff t)))

theorem GalerkinSolution.rhsSobolev_eq_finiteSobolev
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    g.rhsSobolev s t = finiteSobolev s N (galerkinRhs ν N (g.coeff t)) := by
  change finiteStateSobolev s N
      (restrictFiniteState N (galerkinRhs ν N
        (extendFiniteState N (restrictFiniteState N (g.coeff t))))) = _
  rw [finiteStateSobolev_restrict, g.extend_restrict_coeff t ht]

theorem GalerkinSolution.sobolevState_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (g.sobolevState s) (g.rhsSobolev s t) (Ici 0) t := by
  have h := (finiteStateSobolev s N).hasFDerivAt.comp_hasDerivWithinAt t
    (g.finite_hasDerivWithinAt ht)
  simpa only [Function.comp_def, finiteStateSobolev_restrict,
    GalerkinSolution.sobolevState, GalerkinSolution.rhsSobolev] using! h

theorem GalerkinSolution.sobolevState_derivWithin
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    derivWithin (g.sobolevState s) (Ici 0) t = g.rhsSobolev s t :=
  (g.sobolevState_hasDerivWithinAt s t ht).derivWithin ((uniqueDiffOn_Ici 0) t ht)

theorem GalerkinSolution.rhsSobolev_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (s : ℕ) :
    ContinuousOn (g.rhsSobolev s) (Ici 0) := by
  have h := ((finiteStateSobolev s N).continuous.comp
    (contDiff_finiteGalerkinRhs ν N).continuous).comp_continuousOn g.finite_continuousOn
  simpa only [Function.comp_def, GalerkinSolution.rhsSobolev] using! h

private theorem continuousOn_memLp_Icc {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (T : ℝ) (p : ℝ≥0∞) (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    MemLp f p (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) := ⟨by simp⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

/-- Actual path membership, including every finite exponent and the bounded exponent. -/
theorem GalerkinSolution.sobolevState_memLp
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (T : ℝ) (p : ℝ≥0∞) :
    MemLp (g.sobolevState s) p (volume.restrict (Icc (0 : ℝ) T)) :=
  continuousOn_memLp_Icc _ T p
    ((g.sobolevState_continuousOn s).mono (fun t ht => ht.1))

theorem GalerkinSolution.rhsSobolev_memLp
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (s : ℕ) (T : ℝ) (p : ℝ≥0∞) :
    MemLp (g.rhsSobolev s) p (volume.restrict (Icc (0 : ℝ) T)) :=
  continuousOn_memLp_Icc _ T p
    ((g.rhsSobolev_continuousOn s).mono (fun t ht => ht.1))

/-- The actual H0 derivative norm is the literal physical time-derivative L² integral. -/
theorem GalerkinSolution.rhsSobolev_H0_physical_norm_sq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖g.rhsSobolev 0 t‖ ^ 2 =
      ∫ x in unitCube, ‖timeDerivative g.velocity t x‖ ^ 2 := by
  rw [g.rhsSobolev_eq_finiteSobolev 0 t ht, finiteSobolev_norm_sq]
  simp only [pow_zero, one_mul]
  change coefficientEnergy N (galerkinRhs ν N (g.coeff t)) = _
  rw [g.timeDerivative_eq_finiteSynthesis t ht, ← physicalEnergy_eq_integral_norm_sq]
  exact (FINITE_PHYSICAL_ENERGY_PARSEVAL N _
    (galerkinRhs_reality ν N (g.coeff t) (g.real_symmetry t ht))).symm

end

end SingularClosure
