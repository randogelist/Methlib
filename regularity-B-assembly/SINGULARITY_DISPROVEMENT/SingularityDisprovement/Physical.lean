import SingularityDisprovement.Admission
import SingularClosure.CriticalInitialPhysicalFourier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Physical-realization and positive-measure adapters.

These lemmas do not posit a dyadic representative or essential unboundedness.
They isolate the physical L2 convergence and measure-theoretic transport used
by the concrete dyadic proof. The dyadic analytic instance is separate.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory SingularClosure
open scoped Topology ENNReal BigOperators

namespace SingularityDisprovement
noncomputable section

/-- The actual real finite Fourier polynomials converge in physical cube L2. -/
theorem physicalCutoff_tendsto
    (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    Tendsto (fun N : ℕ => physicalFieldL2
      (finiteSynthesis N (criticalCoeff 1 a))
      (finiteSynthesis_contDiff N (criticalCoeff 1 a)).continuous)
      atTop (𝓝 (criticalInitialPhysicalL2 a)) := by
  have h := criticalInitialPhysicalL2_continuous.continuousAt.tendsto.comp
    (criticalFiniteSobolev_tendsto 1 a hzero)
  simpa only [Function.comp_def, criticalInitialPhysicalL2_finite a hreal] using h

/-- Fourier recovery concerns the actual initial physical representative. -/
theorem initialPhysical_fourier_recovery
    (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    datumFourierCoeff (criticalInitialPhysicalL2 a : Field) = criticalCoeff 1 a :=
  criticalInitialPhysicalL2_fourierCoeff a hreal hzero

/-- A pointwise a.e. limit of these same Fourier polynomials must be the
native physical representative. No physical equality is assumed. -/
theorem physicalCutoff_ae_limit_unique
    (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (g : Field)
    (hg : ∀ᵐ x ∂volume.restrict unitCube,
      Tendsto (fun N : ℕ => finiteSynthesis N (criticalCoeff 1 a) x)
        atTop (𝓝 (g x))) :
    (criticalInitialPhysicalL2 a : Field) =ᵐ[volume.restrict unitCube] g := by
  haveI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by rw [Measure.restrict_apply_univ];
        exact isCompact_unitCube.measure_lt_top (μ := volume)⟩
  have hLp := tendstoInMeasure_of_tendsto_Lp
    (physicalCutoff_tendsto a hreal hzero)
  have hpoly : TendstoInMeasure (volume.restrict unitCube)
      (fun N : ℕ => finiteSynthesis N (criticalCoeff 1 a))
      atTop (criticalInitialPhysicalL2 a : Field) :=
    TendstoInMeasure.congr_left
      (fun N => physicalFieldL2_coe _
        (finiteSynthesis_contDiff N (criticalCoeff 1 a)).continuous) hLp
  have hgmeasure := tendstoInMeasure_of_tendsto_ae
    (fun N => (finiteSynthesis_contDiff N (criticalCoeff 1 a)).continuous.aestronglyMeasurable)
    hg
  exact tendstoInMeasure_ae_unique hpoly hgmeasure

/-- A nonempty open patch inside the cube has positive restricted volume. -/
theorem cube_open_patch_measure_pos
    (U : Set Vec) (hopen : IsOpen U) (hne : U.Nonempty)
    (hsub : U ⊆ unitCube) :
    0 < (volume.restrict unitCube) U := by
  rw [Measure.restrict_apply hopen.measurableSet, Set.inter_eq_left.mpr hsub]
  exact hopen.measure_pos volume hne

/-- An open positive-measure lower-bound patch survives a.e. identification. -/
theorem physical_density_superlevel_pos_of_patch
    (a : CriticalSobolev 1) (g : Field)
    (hrep : (criticalInitialPhysicalL2 a : Field) =ᵐ[volume.restrict unitCube] g)
    (M : ℝ) (U : Set Vec)
    (hopen : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ unitCube)
    (hlarge : ∀ x ∈ U, M < ‖g x‖ ^ 2 / 2) :
    0 < (volume.restrict unitCube)
      {x | M < ‖criticalInitialPhysicalL2 a x‖ ^ 2 / 2} := by
  have hmono : U ≤ᵐ[volume.restrict unitCube]
      {x | M < ‖criticalInitialPhysicalL2 a x‖ ^ 2 / 2} := by
    filter_upwards [hrep] with x hx
    intro hUx
    change M < ‖criticalInitialPhysicalL2 a x‖ ^ 2 / 2
    rw [hx]
    exact hlarge x hUx
  exact lt_of_lt_of_le (cube_open_patch_measure_pos U hopen hne hsub)
    (measure_mono_ae hmono)

/-- Explicit quantification over all finite thresholds. This adapter's
open-patch hypothesis must be supplied by the concrete dyadic lower bound. -/
theorem physical_density_all_superlevels_pos_of_patches
    (a : CriticalSobolev 1) (g : Field)
    (hrep : (criticalInitialPhysicalL2 a : Field) =ᵐ[volume.restrict unitCube] g)
    (hpatch : ∀ M : ℝ, 0 ≤ M → ∃ U : Set Vec,
      IsOpen U ∧ U.Nonempty ∧ U ⊆ unitCube ∧
        ∀ x ∈ U, M < ‖g x‖ ^ 2 / 2) :
    ∀ M : ℝ, 0 ≤ M → 0 < (volume.restrict unitCube)
      {x | M < ‖criticalInitialPhysicalL2 a x‖ ^ 2 / 2} := by
  intro M hM
  obtain ⟨U, hopen, hne, hsub, hlarge⟩ := hpatch M hM
  exact physical_density_superlevel_pos_of_patch a g hrep M U hopen hne hsub hlarge

end
end SingularityDisprovement
