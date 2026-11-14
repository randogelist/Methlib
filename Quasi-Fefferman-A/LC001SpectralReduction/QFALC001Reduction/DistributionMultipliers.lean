import QFALC001Reduction.NativeFromAENorms

/-!
# Distributional derivative witnesses to Fourier multiplier representatives

This module converts exact tempered-distribution Fourier multiplier identities
into almost-everywhere identities for the chosen `L2` representatives.  The
norm-density aggregation is deliberately left to the next module.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform SchwartzMap LineDeriv Laplacian

namespace QFA.LC001SpectralReduction

open QFA.Endpoints.Agmon

noncomputable section

/-- Equality of a Fourier-side `L2` distribution with a scalar multiple of a
real continuous multiplier determines the chosen representatives almost
everywhere. -/
theorem ae_eq_of_const_smul_real_multiplier_distribution
    (q h : ComplexL2) (c : ℂ) (m : Space → ℝ)
    (hm_cont : Continuous m) (hm_temp : m.HasTemperateGrowth)
    (hEq : (q : 𝓢'(Space, ComplexVector)) =
      c • TemperedDistribution.smulLeftCLM ComplexVector m
        (h : 𝓢'(Space, ComplexVector))) :
    (fun x : Space => q x) =ᵐ[volume]
      (fun x : Space => (c * (m x : ℂ)) • h x) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp q).locallyIntegrable (by norm_num)
  · exact continuous_smul (by fun_prop)
      ((Lp.memLp h).locallyIntegrable (by norm_num))
  · intro g hg g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let φ : 𝓢(Space, ℂ) := hg₁.toSchwartzMap hg₂
    have hEval := congrArg (fun T : 𝓢'(Space, ComplexVector) => T φ) hEq
    simpa [φ, Function.comp_apply, hm_temp, smul_smul, mul_assoc, mul_left_comm,
      mul_comm] using hEval

/-- Fourier transform of each supplied first derivative, as an exact equality
of tempered distributions. -/
theorem gradient_fourier_distribution_eq
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) (j : Fin 3) :
    ((𝓕 (G j) : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (inner ℝ · EuclideanSpace.basisFun (Fin 3) ℝ j)
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
  calc
    ((𝓕 (G j) : ComplexL2) : 𝓢'(Space, ComplexVector)) =
        𝓕 ((G j : ComplexL2) : 𝓢'(Space, ComplexVector)) :=
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq (G j)).symm
    _ = 𝓕 (∂_{EuclideanSpace.basisFun (Fin 3) ℝ j}
        (v : 𝓢'(Space, ComplexVector))) := by rw [← h.gradient_eq j]
    _ = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (inner ℝ · EuclideanSpace.basisFun (Fin 3) ℝ j)
          (𝓕 (v : 𝓢'(Space, ComplexVector))) :=
      TemperedDistribution.fourier_lineDerivOp_eq
        (v : 𝓢'(Space, ComplexVector)) (EuclideanSpace.basisFun (Fin 3) ℝ j)
    _ = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (inner ℝ · EuclideanSpace.basisFun (Fin 3) ℝ j)
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
      rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq v]

/-- Almost-everywhere first-derivative multiplier identity. -/
theorem gradient_fourier_ae
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) (j : Fin 3) :
    (fun k : Space => (𝓕 (G j) : ComplexL2) k) =ᵐ[volume]
      (fun k : Space =>
        ((2 * Real.pi * Complex.I) *
          (inner ℝ k (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ)) •
            (𝓕 v : ComplexL2) k) := by
  exact ae_eq_of_const_smul_real_multiplier_distribution
    (𝓕 (G j) : ComplexL2) (𝓕 v : ComplexL2)
    (2 * Real.pi * Complex.I)
    (inner ℝ · EuclideanSpace.basisFun (Fin 3) ℝ j)
    (by fun_prop) (by fun_prop) (gradient_fourier_distribution_eq h j)

/-- Fourier transform of the supplied Laplacian, as an exact equality of
tempered distributions. -/
theorem laplacian_fourier_distribution_eq
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    ((𝓕 L : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => ‖k‖ ^ 2)
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
  calc
    ((𝓕 L : ComplexL2) : 𝓢'(Space, ComplexVector)) =
        𝓕 (L : 𝓢'(Space, ComplexVector)) :=
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq L).symm
    _ = 𝓕 (Δ (v : 𝓢'(Space, ComplexVector))) := by rw [← h.laplacian_eq]
    _ = (-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => ‖k‖ ^ 2)
          (𝓕 (v : 𝓢'(Space, ComplexVector))) := by
      rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
      simp [TemperedDistribution.fourierMultiplierCLM_apply]
    _ = (-(2 * Real.pi) ^ 2 : ℂ) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => ‖k‖ ^ 2)
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
      rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq v]

/-- Almost-everywhere Laplacian multiplier identity. -/
theorem laplacian_fourier_ae
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    (fun k : Space => (𝓕 L : ComplexL2) k) =ᵐ[volume]
      (fun k : Space =>
        ((-(2 * Real.pi) ^ 2 : ℂ) * (‖k‖ ^ 2 : ℂ)) •
          (𝓕 v : ComplexL2) k) := by
  exact ae_eq_of_const_smul_real_multiplier_distribution
    (𝓕 L : ComplexL2) (𝓕 v : ComplexL2)
    (-(2 * Real.pi) ^ 2 : ℂ) (fun k : Space => ‖k‖ ^ 2)
    (by fun_prop) (by fun_prop) (laplacian_fourier_distribution_eq h)

end

end QFA.LC001SpectralReduction
