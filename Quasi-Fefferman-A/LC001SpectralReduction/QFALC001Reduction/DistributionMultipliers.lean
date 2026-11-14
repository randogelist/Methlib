import QFALC001Reduction.NativeFromAENorms

/-!
# Distributional derivative witnesses to Fourier multiplier representatives

This module converts exact tempered-distribution Fourier multiplier identities
into almost-everywhere identities for the chosen `L2` representatives. The
norm-density aggregation is deliberately left to the next module.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory FourierTransform
open scoped Nat NNReal ContDiff BigOperators FourierTransform SchwartzMap LineDeriv Laplacian

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
      c • TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : Space => (m x : ℂ))
        (h : 𝓢'(Space, ComplexVector))) :
    (fun x : Space => q x) =ᵐ[volume]
      (fun x : Space => (c * (m x : ℂ)) • h x) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp q).locallyIntegrable (by norm_num)
  · exact MeasureTheory.LocallyIntegrable.continuous_smul (by fun_prop)
      ((Lp.memLp h).locallyIntegrable (by norm_num))
  · intro g hg g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let test := hg₁.toSchwartzMap hg₂
    have hEval := congrArg (fun T : 𝓢'(Space, ComplexVector) => T test) hEq
    rw [SchwartzMap.smulLeftCLM_apply hm_temp test] at hEval
    calc
      (∫ x : Space, g x • q x) =
          c • ∫ x : Space, ((m x : ℂ) * (g x : ℂ)) • h x := by
        simpa [test, Function.comp_apply, smul_smul, mul_assoc, mul_left_comm,
          mul_comm] using hEval
      _ = ∫ x : Space, c • (((m x : ℂ) * (g x : ℂ)) • h x) := by
        rw [integral_smul]
      _ = ∫ x : Space, g x • ((c * (m x : ℂ)) • h x) := by
        apply integral_congr_ae
        filter_upwards with x
        calc
          c • (((m x : ℂ) * (g x : ℂ)) • h x) =
              (c * ((m x : ℂ) * (g x : ℂ))) • h x :=
            (mul_smul c ((m x : ℂ) * (g x : ℂ)) (h x)).symm
          _ = ((g x : ℂ) * (c * (m x : ℂ))) • h x := by
            congr 1
            ring
          _ = (g x : ℂ) • ((c * (m x : ℂ)) • h x) :=
            mul_smul (g x : ℂ) (c * (m x : ℂ)) (h x)
          _ = g x • ((c * (m x : ℂ)) • h x) :=
            (RCLike.real_smul_eq_coe_smul (K := ℂ) (g x)
              ((c * (m x : ℂ)) • h x)).symm

/-- Fourier transform of each supplied first derivative, as an exact equality
of tempered distributions. -/
theorem gradient_fourier_distribution_eq
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) (j : Fin 3) :
    ((𝓕 (G j) : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun x : Space =>
            (inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ))
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
  calc
    ((𝓕 (G j) : ComplexL2) : 𝓢'(Space, ComplexVector)) =
        𝓕 ((G j : ComplexL2) : 𝓢'(Space, ComplexVector)) :=
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq (G j)).symm
    _ = 𝓕 (∂_{EuclideanSpace.basisFun (Fin 3) ℝ j}
        (v : 𝓢'(Space, ComplexVector))) := by rw [← h.gradient_eq j]
    _ = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun x : Space =>
            (inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ))
          (𝓕 (v : 𝓢'(Space, ComplexVector))) := by
      simpa using
        (TemperedDistribution.fourier_lineDerivOp_eq
          (v : 𝓢'(Space, ComplexVector)) (EuclideanSpace.basisFun (Fin 3) ℝ j))
    _ = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun x : Space =>
            (inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ))
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
    (fun k : Space => inner ℝ k (EuclideanSpace.basisFun (Fin 3) ℝ j))
    (by fun_prop) (by fun_prop) (gradient_fourier_distribution_eq h j)

/-- Fourier transform of the supplied Laplacian, as an exact equality of
tempered distributions. -/
theorem laplacian_fourier_distribution_eq
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    ((𝓕 L : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (-((2 * Real.pi) ^ 2)) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => (‖k‖ ^ 2 : ℂ))
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
  let f : 𝓢'(Space, ComplexVector) := (v : 𝓢'(Space, ComplexVector))
  let M : 𝓢'(Space, ComplexVector) :=
    TemperedDistribution.fourierMultiplierCLM ComplexVector
      (fun k : Space => (‖k‖ ^ 2 : ℂ)) f
  calc
    ((𝓕 L : ComplexL2) : 𝓢'(Space, ComplexVector)) =
        𝓕 (L : 𝓢'(Space, ComplexVector)) :=
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq L).symm
    _ = 𝓕 (Δ f) := by simpa [f] using congrArg 𝓕 h.laplacian_eq
    _ = 𝓕 (-((2 * Real.pi) ^ 2 • M)) := by
      congr 1
      simpa [M] using
        (TemperedDistribution.laplacian_eq_fourierMultiplierCLM f)
    _ = -(𝓕 ((2 * Real.pi) ^ 2 • M)) := by
      simpa using (fourier_neg (((2 * Real.pi) ^ 2) • M))
    _ = -((2 * Real.pi) ^ 2 • 𝓕 M) := by
      exact congrArg (fun z : 𝓢'(Space, ComplexVector) => -z)
        (ContinuousLinearMap.map_smul_of_tower
          (FourierTransform.fourierCLM ℂ (𝓢'(Space, ComplexVector)))
          ((2 * Real.pi) ^ 2) M)
    _ = -((2 * Real.pi) ^ 2 •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => (‖k‖ ^ 2 : ℂ)) (𝓕 f)) := by
      simp [M, TemperedDistribution.fourierMultiplierCLM_apply]
    _ = -((2 * Real.pi) ^ 2 •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => (‖k‖ ^ 2 : ℂ))
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector))) := by
      simp [f, MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    _ = (-((2 * Real.pi) ^ 2)) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => (‖k‖ ^ 2 : ℂ))
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
      symm
      exact neg_smul ((2 * Real.pi) ^ 2)
        (TemperedDistribution.smulLeftCLM ComplexVector
          (fun k : Space => (‖k‖ ^ 2 : ℂ))
          ((𝓕 v : ComplexL2) : 𝓢'(Space, ComplexVector)))

/-- Almost-everywhere Laplacian multiplier identity in the complex scalar
normalization used by the norm-density calculation. -/
set_option maxHeartbeats 800000 in
theorem laplacian_fourier_ae
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    (fun k : Space => (𝓕 L : ComplexL2) k) =ᵐ[volume]
      (fun k : Space =>
        ((-((2 * Real.pi) ^ 2) : ℂ) * (‖k‖ ^ 2 : ℂ)) •
          (𝓕 v : ComplexL2) k) := by
  apply ae_eq_of_const_smul_real_multiplier_distribution
    (𝓕 L : ComplexL2) (𝓕 v : ComplexL2)
    (-((2 * Real.pi) ^ 2) : ℂ) (fun k : Space => ‖k‖ ^ 2)
    (by fun_prop) (by fun_prop)
  simpa only [Complex.real_smul] using laplacian_fourier_distribution_eq h

end

end QFA.LC001SpectralReduction
