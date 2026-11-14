import QFA.Endpoints.Agmon.Contracts
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Native spectral realization from a.e. Fourier norm identities

The input records only the two nontrivial multiplier consequences:

* the sum of the squared Fourier norms of the three first derivatives equals
  `(2*pi)^2 * ‖k‖^2 * ‖hat v(k)‖^2` almost everywhere;
* the squared Fourier norm of the Laplacian equals
  `(2*pi)^4 * ‖k‖^4 * ‖hat v(k)‖^2` almost everywhere.

Plancherel and the generic `L2` norm-integral identity then supply every field
of `NativeSpectralRealization`.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform InnerProductSpace

namespace QFA.LC001SpectralReduction

open QFA.Endpoints.Agmon

noncomputable section

/-- Fourier energy density. -/
def energyDensity (v : ComplexL2) (k : Space) : ℝ :=
  ‖(𝓕 v : ComplexL2) k‖ ^ 2

/-- Fourier gradient density in the native QFA normalization. -/
def gradientDensity (v : ComplexL2) (k : Space) : ℝ :=
  (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * energyDensity v k

/-- Fourier Laplacian density in the native QFA normalization. -/
def laplacianDensity (v : ComplexL2) (k : Space) : ℝ :=
  (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * energyDensity v k

/-- The exact a.e. norm identities left after Fourier-transforming the weak
first- and second-derivative equations. -/
structure FourierNormAEWitnesses
    (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2) : Prop where
  gradient_ae :
    (fun k : Space => ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2) =ᵐ[volume]
      gradientDensity v
  laplacian_ae :
    (fun k : Space => ‖(𝓕 L : ComplexL2) k‖ ^ 2) =ᵐ[volume]
      laplacianDensity v

/-- Every `L2` representative has an integrable squared pointwise norm. -/
theorem integrable_norm_sq (f : ComplexL2) :
    Integrable (fun x : Space => ‖f x‖ ^ 2) volume := by
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

/-- The square of the `L2` norm is the integral of the squared pointwise norm. -/
theorem integral_norm_sq_eq_norm_sq (f : ComplexL2) :
    (∫ x : Space, ‖f x‖ ^ 2 ∂volume) = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h.symm
  · exact L2.integrable_inner f f

/-- The finite sum of the three Fourier derivative norm densities is
integrable. -/
theorem integrable_gradient_fourier_sum (G : Fin 3 → ComplexL2) :
    Integrable (fun k : Space => ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2) volume := by
  exact Integrable.sum Finset.univ (fun j _ => integrable_norm_sq (𝓕 (G j) : ComplexL2))

/-- The integral of the finite derivative sum equals the sum of the three
Fourier `L2` norm squares. -/
theorem integral_gradient_fourier_sum (G : Fin 3 → ComplexL2) :
    (∫ k : Space, ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2 ∂volume) =
      ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2)‖ ^ 2 := by
  calc
    (∫ k : Space, ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2 ∂volume) =
        ∑ j : Fin 3, ∫ k : Space, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2 ∂volume := by
      simpa using (integral_finsetSum Finset.univ
        (fun j _ => integrable_norm_sq (𝓕 (G j) : ComplexL2)))
    _ = ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_norm_sq_eq_norm_sq (𝓕 (G j) : ComplexL2)

/-- The two a.e. norm identities imply all six native spectral fields. -/
theorem nativeSpectralRealization_of_fourierNormAE
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : FourierNormAEWitnesses v G L) :
    NativeSpectralRealization v G L := by
  have hEnergyInt : Integrable (energyDensity v) volume := by
    simpa only [energyDensity] using integrable_norm_sq (𝓕 v : ComplexL2)
  have hGradientInt : Integrable (gradientDensity v) volume :=
    (integrable_gradient_fourier_sum G).congr h.gradient_ae
  have hLaplacianInt : Integrable (laplacianDensity v) volume :=
    (integrable_norm_sq (𝓕 L : ComplexL2)).congr h.laplacian_ae
  refine
    { energy_integrable := by
        simpa only [energyDensity] using hEnergyInt
      gradient_integrable := by
        simpa only [gradientDensity, energyDensity] using hGradientInt
      laplacian_integrable := by
        simpa only [laplacianDensity, energyDensity] using hLaplacianInt
      energy_identity := ?_
      gradient_identity := ?_
      laplacian_identity := ?_ }
  · calc
      velocityEnergy v = ‖v‖ ^ 2 := rfl
      _ = ‖(𝓕 v : ComplexL2)‖ ^ 2 := by
        rw [MeasureTheory.Lp.norm_fourier_eq]
      _ = ∫ k : Space, ‖(𝓕 v : ComplexL2) k‖ ^ 2 ∂volume :=
        (integral_norm_sq_eq_norm_sq (𝓕 v : ComplexL2)).symm
  · calc
      gradientEnergy G = ∑ j : Fin 3, ‖G j‖ ^ 2 := rfl
      _ = ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [MeasureTheory.Lp.norm_fourier_eq]
      _ = ∫ k : Space, ∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2 ∂volume :=
        (integral_gradient_fourier_sum G).symm
      _ = ∫ k : Space, gradientDensity v k ∂volume :=
        integral_congr_ae h.gradient_ae
      _ = ∫ k : Space,
          (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2 ∂volume := by
        rfl
  · calc
      laplacianEnergy L = ‖L‖ ^ 2 := rfl
      _ = ‖(𝓕 L : ComplexL2)‖ ^ 2 := by
        rw [MeasureTheory.Lp.norm_fourier_eq]
      _ = ∫ k : Space, ‖(𝓕 L : ComplexL2) k‖ ^ 2 ∂volume :=
        (integral_norm_sq_eq_norm_sq (𝓕 L : ComplexL2)).symm
      _ = ∫ k : Space, laplacianDensity v k ∂volume :=
        integral_congr_ae h.laplacian_ae
      _ = ∫ k : Space,
          (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * ‖(𝓕 v : ComplexL2) k‖ ^ 2 ∂volume := by
        rfl

/-- The remaining LC001 endpoint after the a.e. multiplier consequences have
been supplied. -/
def FourierNormAEToNativeSpectralEndpoint : Prop :=
  ∀ (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2),
    FourierNormAEWitnesses v G L → NativeSpectralRealization v G L

/-- Kernel-level reduction of LC001 to the two a.e. norm identities. -/
theorem fourierNormAEToNativeSpectralEndpoint :
    FourierNormAEToNativeSpectralEndpoint := by
  intro v G L h
  exact nativeSpectralRealization_of_fourierNormAE h

end

end QFA.LC001SpectralReduction
