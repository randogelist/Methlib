import SingularClosure.GalerkinInvariant
import SingularClosure.GalerkinExistence
import SingularClosure.InitialFourier
import SingularClosure.FiniteParseval

/-!
# Actual Galerkin trajectories from rough Fourier data

The initial input is a coefficient function, rather than a smooth physical
datum. At cutoff N its real finite synthesis is an actual physical datum.
Its Fourier coefficients are proved to be exactly the cutoff of the input.
The existing invariant finite-dimensional solver therefore supplies the
original GalerkinSolution structure, with its literal polynomial equation.

No fractional regularity is needed for this finite construction. In
particular, a weighted-l2 critical datum can use the construction directly
through its coefficient function and the actual spectral constraints.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem criticalGalerkin_fourier_integrable (N : ℕ) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) :
    IntegrableOn (datumFourierIntegrand (finiteSynthesis N c) k i) unitCube volume :=
  datumFourierIntegrand_integrableOn (finiteSynthesis_contDiff N c).continuous k i

private theorem criticalGalerkin_integral_character_coefficient
    (k l : Frequency) (z : ℂ) :
    (∫ x in unitCube, star (fourierCharacter k x) * (fourierCharacter l x * z)) =
      if k = l then z else 0 := by
  simpa only [mul_one, star_one, one_mul] using
    integral_complex_character_pair k l 1 z

/-- Actual physical Fourier integration recovers precisely the input cutoff. -/
theorem criticalGalerkin_datumFourierCoeff_finiteSynthesis
    (N : ℕ) (c : FourierCoeff) (hreal : SpectralReality c) :
    datumFourierCoeff (finiteSynthesis N c) = cutoffCoeff N c := by
  classical
  funext k i
  have hpoint : datumFourierIntegrand (finiteSynthesis N c) k i =
      fun x => ∑ l ∈ cutoffModes N,
        star (fourierCharacter k x) * (fourierCharacter l x * c l i) := by
    funext x
    change star (fourierCharacter k x) * (finiteSynthesis N c x i : ℂ) = _
    rw [← complexFiniteSynthesis_eq_ofReal N c hreal i x]
    simp only [complexFiniteSynthesis, Finset.mul_sum]
  change (∫ x in unitCube, datumFourierIntegrand (finiteSynthesis N c) k i x) = _
  rw [hpoint]
  change (∫ x in unitCube, ∑ l ∈ cutoffModes N,
    star (fourierCharacter k x) * (fourierCharacter l x * c l i)) = cutoffCoeff N c k i
  rw [integral_finsetSum (cutoffModes N)
    (f := fun l x => star (fourierCharacter k x) *
      (fourierCharacter l x * c l i))
    (μ := volume.restrict unitCube) (fun l _ =>
      ((fourierCharacter_contDiff k).continuous.star.mul
        ((fourierCharacter_contDiff l).continuous.mul continuous_const)).continuousOn.integrableOn_compact
          isCompact_unitCube)]
  simp_rw [criticalGalerkin_integral_character_coefficient]
  change (∑ l ∈ cutoffModes N, if k = l then c l i else 0) =
    if k ∈ cutoffModes N then c k i else 0
  by_cases hk : k ∈ cutoffModes N
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp only [ite_true]
    · intro l _ hl
      exact if_neg (Ne.symm hl)
    · intro hnot
      exact (hnot hk).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro l hl
    have hne : k ≠ l := by
      intro h
      exact hk (h.symm ▸ hl)
    exact if_neg hne

/-- Every original Galerkin trajectory for the synthesized cutoff has the
specified coefficient initial value. This is a proved Fourier identity. -/
theorem criticalGalerkin_initial_coeff
    {ν : ℝ} {N : ℕ} {c : FourierCoeff} (hreal : SpectralReality c)
    (g : GalerkinSolution ν (finiteSynthesis N c) N) :
    g.coeff 0 = cutoffCoeff N c := by
  have hinit : g.coeff 0 = cutoffCoeff N (datumFourierCoeff (finiteSynthesis N c)) := by
    funext k i
    exact g.initial k i
  rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal,
    cutoffCoeff_idempotent] at hinit
  exact hinit

theorem criticalGalerkin_initial_velocity
    {ν : ℝ} {N : ℕ} {c : FourierCoeff} (hreal : SpectralReality c)
    (g : GalerkinSolution ν (finiteSynthesis N c) N) :
    g.velocity 0 = finiteSynthesis N c := by
  change finiteSynthesis N (g.coeff 0) = finiteSynthesis N c
  rw [criticalGalerkin_initial_coeff hreal g, finiteSynthesis_cutoffCoeff]

/-- Equality of the actual initial coefficients is sufficient for uniqueness;
the names or representatives of the physical initial data may differ. -/
theorem criticalGalerkin_coeff_unique_of_initial
    {ν : ℝ} {a b : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (h : GalerkinSolution ν b N)
    (hinit : g.coeff 0 = h.coeff 0) : EqOn g.coeff h.coeff (Ici 0) := by
  intro t ht
  have hrestrict : restrictFiniteState N (g.coeff 0) =
      restrictFiniteState N (h.coeff 0) := congrArg (restrictFiniteState N) hinit
  have heq := finiteGalerkinRhs_unique_on_Icc ν N
    (fun s => restrictFiniteState N (g.coeff s))
    (fun s => restrictFiniteState N (h.coeff s)) t
    g.finite_continuousOn h.finite_continuousOn
    (fun _ hs => g.finite_hasDerivWithinAt hs)
    (fun _ hs => h.finite_hasDerivWithinAt hs) hrestrict
    ⟨ht, le_rfl⟩
  have hext := congrArg (extendFiniteState N) heq
  simpa only [g.extend_restrict_coeff t ht, h.extend_restrict_coeff t ht] using hext

/-- The original actual finite NSE solver applies to every real solenoidal
coefficient datum, irrespective of its untruncated spatial smoothness. -/
theorem CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    ∃ g : GalerkinSolution ν (finiteSynthesis N c) N,
      g.coeff 0 = cutoffCoeff N c ∧
        ∀ h : GalerkinSolution ν (finiteSynthesis N c) N,
          EqOn g.coeff h.coeff (Ici 0) := by
  have hrealN : SpectralReality (datumFourierCoeff (finiteSynthesis N c)) := by
    rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal]
    exact cutoffCoeff_preserves_reality N hreal
  have hsolN : SpectralSolenoidal (datumFourierCoeff (finiteSynthesis N c)) := by
    rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal]
    exact cutoffCoeff_preserves_solenoidal N hsol
  obtain ⟨g⟩ := galerkinSolution_exists_of_fourier_invariants ν hν
    (finiteSynthesis N c) N (criticalGalerkin_fourier_integrable N c) hrealN hsolN
  exact ⟨g, criticalGalerkin_initial_coeff hreal g, fun h => g.coeff_unique_forward h⟩

/-- A canonical family of the original GalerkinSolution objects, initialized
by the literal cutoff of a single possibly rough coefficient datum. -/
def criticalGalerkinSolution
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    GalerkinSolution ν (finiteSynthesis N c) N :=
  (CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν c hreal hsol N).choose

theorem criticalGalerkinSolution_initial
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    (criticalGalerkinSolution ν hν c hreal hsol N).coeff 0 = cutoffCoeff N c :=
  (CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν c hreal hsol N).choose_spec.1

theorem criticalGalerkinSolution_unique
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ)
    {a : Field} (g : GalerkinSolution ν a N)
    (hinit : g.coeff 0 = cutoffCoeff N c) :
    EqOn (criticalGalerkinSolution ν hν c hreal hsol N).coeff g.coeff (Ici 0) := by
  apply criticalGalerkin_coeff_unique_of_initial
  exact (criticalGalerkinSolution_initial ν hν c hreal hsol N).trans hinit.symm

theorem criticalGalerkinSolution_initial_velocity
    (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    (criticalGalerkinSolution ν hν c hreal hsol N).velocity 0 = finiteSynthesis N c :=
  criticalGalerkin_initial_velocity hreal _

end

end SingularClosure
