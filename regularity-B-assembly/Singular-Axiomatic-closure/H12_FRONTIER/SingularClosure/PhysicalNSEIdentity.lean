import SingularClosure.InfiniteFourierPressure
import SingularClosure.SmoothFourierLaplacian
import SingularClosure.PeriodicFourierInjective
import SingularClosure.StrongCoefficientContracts

/-! Literal pointwise NSE recovery from the concrete full Fourier equation. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace SingularClosure

noncomputable section

theorem fullFourierRhs_reality (ν : ℝ) (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val) :
    SpectralReality (fullFourierRhs ν c) := by
  have hb := divergenceTransport_reality c hc hreal hsol
  intro k i
  have he : fullTransportCoefficients c (-k) =
      fun j => star (fullTransportCoefficients c k j) := funext (fun j => hb k j)
  have hf : galerkinFreqSq (-k) = galerkinFreqSq k := by simp [galerkinFreqSq]
  change -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq (-k) : ℝ) : ℝ) : ℂ) *
      c.val (-k) i - coefficientLeray (-k) (fullTransportCoefficients c (-k)) i =
    star (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
      c.val k i - coefficientLeray k (fullTransportCoefficients c k) i)
  rw [hf, hreal k i, he, coefficientLeray_neg_star]
  simp

/-- The pressure and convection are literal physical derivatives. Fourier
injectivity converts the actual coefficient identity into the pointwise NSE. -/
theorem PHYSICAL_NSE_OF_FULL_FOURIER_RHS (ν : ℝ) (c : TorusSobolev 0)
    (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c.val) 2)
    (hreal : SpectralReality c.val) (hsol : SpectralSolenoidal c.val)
    (hr : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s (fullFourierRhs ν c)) 2) :
    ∀ x : Vec,
      smoothFourierSynthesis (fullFourierRhs ν c) x +
        convection (smoothFourierSynthesis c.val) x +
        gradient (fullTransportPressure c) x =
          ν • laplacian (smoothFourierSynthesis c.val) x := by
  let u : Field := smoothFourierSynthesis c.val
  let v : Field := smoothFourierSynthesis (fullFourierRhs ν c)
  let p : Vec → ℝ := fullTransportPressure c
  have hcu := smoothFourierSynthesis_contDiff c.val (ALL_SOBOLEV_IMP_RAPID_SCALAR c.val hc)
  have hcv := smoothFourierSynthesis_contDiff (fullFourierRhs ν c)
    (ALL_SOBOLEV_IMP_RAPID_SCALAR (fullFourierRhs ν c) hr)
  have hpu : SpatialPeriodic u := smoothFourierSynthesis_periodic c.val
  have hpv : SpatialPeriodic v := smoothFourierSynthesis_periodic _
  have hg : gradient p = smoothFourierSynthesis
      (fun k i => coefficientLeray k (fullTransportCoefficients c k) i -
        fullTransportCoefficients c k i) :=
    infiniteTransportPressure_gradient _ (divergenceTransport_rapid c hc hreal hsol)
  have hcg : Continuous (gradient p) := by
    rw [hg]
    exact (smoothFourierSynthesis_contDiff _
      (infinitePressureGradient_rapid _ (divergenceTransport_rapid c hc hreal hsol))).continuous
  have hpg : SpatialPeriodic (gradient p) := by
    rw [hg]
    exact smoothFourierSynthesis_periodic _
  have hconv : Continuous (convection u) := (convection_contDiff u hcu).continuous
  have hpc : SpatialPeriodic (convection u) := convection_periodic u hpu
  have hlap : Continuous (laplacian u) := (laplacian_contDiff u hcu).continuous
  have hpl : SpatialPeriodic (laplacian u) := laplacian_spatialPeriodic u hpu
  have hleft : SpatialPeriodic ((v + convection u) + gradient p) := by
    intro x i
    change (v (x + unitVector i) + convection u (x + unitVector i)) +
      gradient p (x + unitVector i) = (v x + convection u x) + gradient p x
    rw [hpv x i, hpc x i, hpg x i]
  have hright : SpatialPeriodic (ν • laplacian u) := by
    intro x i
    change ν • laplacian u (x + unitVector i) = ν • laplacian u x
    rw [hpl x i]
  have hcoeff : datumFourierCoeff ((v + convection u) + gradient p) =
      datumFourierCoeff (ν • laplacian u) := by
    rw [datumFourierCoeff_add _ _ (hcv.continuous.add hconv) hcg,
      datumFourierCoeff_add _ _ hcv.continuous hconv,
      datumFourierCoeff_real_smul]
    have hvcoeff : datumFourierCoeff v = fullFourierRhs ν c :=
      datumFourierCoeff_smoothFourierSynthesis _ (ALL_SOBOLEV_IMP_RAPID_SCALAR _ hr)
        (fullFourierRhs_reality ν c hc hreal hsol)
    rw [hvcoeff, smoothFourierSynthesis_convection_coeff c hc hreal hsol,
      fullTransportPressure_gradient_coeff c hc hreal hsol,
      smoothFourierSynthesis_laplacian_coeff c.val
        (ALL_SOBOLEV_IMP_RAPID_SCALAR c.val hc) hreal]
    funext k i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold fullFourierRhs laplacianCoefficient laplacianFrequency
    change _ + _ + (coefficientLeray k (fullTransportCoefficients c k) i -
      fullTransportCoefficients c k i) = _
    change -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i -
        coefficientLeray k (fullTransportCoefficients c k) i + fullTransportCoefficients c k i +
        (coefficientLeray k (fullTransportCoefficients c k) i - fullTransportCoefficients c k i) =
      (ν : ℂ) * (-(((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i)
    push_cast
    ring
  have heq := datumFourierCoeff_injective_continuous_periodic
    ((v + convection u) + gradient p) (ν • laplacian u)
    ((hcv.continuous.add hconv).add hcg) (hlap.const_smul ν) hleft hright hcoeff
  intro x
  exact congrFun heq x

end

end SingularClosure
