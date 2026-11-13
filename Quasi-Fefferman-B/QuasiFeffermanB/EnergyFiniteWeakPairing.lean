import SingularClosure.CriticalClassicalWeakMomentum
import SingularClosure.GalerkinTimeDerivative

/-! The exact physical weak pairing of the finite Galerkin vector field.
The pressure projection disappears because the physical test is solenoidal;
the quadratic term is the actual physical transport pairing. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff Interval
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_galerkin_mode_pairing (ν : ℝ) (N : ℕ) (c b : FourierCoeff)
    (hb : SpectralSolenoidal b) (k : Frequency) :
    (∑ i : Fin 3, (star (b k i) * galerkinRhs ν N c k i).re) =
      ν * (∑ i : Fin 3, (star (laplacianCoefficient b k i) * c k i).re) -
        ∑ i : Fin 3, (star (b k i) * coefficientTransport N c k i).re := by
  have hleray := congrArg Complex.re (coefficientLeray_pairing k (b k)
    (coefficientTransport N c k) (hb k))
  simp only [physical_complex_re_sum] at hleray
  simp only [galerkinRhs, mul_sub, Complex.sub_re, Finset.sum_sub_distrib]
  rw [hleray, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [laplacianCoefficient, laplacianFrequency, Complex.star_def,
    Complex.mul_re, Complex.mul_im] <;> ring

theorem ENERGY_FINITE_GALERKIN_WEAK_PAIRING
    (ν : ℝ) (N : ℕ) (c b : FourierCoeff)
    (hcsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hcr : SpectralReality c) (hcs : SpectralSolenoidal c)
    (hbr : SpectralReality b) (hbs : SpectralSolenoidal b) :
    physicalFieldInner (finiteSynthesis N (galerkinRhs ν N c)) (finiteSynthesis N b) =
      ν * physicalFieldInner (finiteSynthesis N c) (laplacian (finiteSynthesis N b)) +
        criticalWeakTransport (finiteSynthesis N c) (finiteSynthesis N b) := by
  have hdiv : ∀ p : Vec → ℝ, ContDiff ℝ ∞ p → SpatialPeriodic p →
      physicalFieldInner (finiteSynthesis N c) (SingularClosure.gradient p) = 0 := by
    intro p hp hpp
    exact critical_smooth_integral_inner_gradient_eq_zero _ p (finiteSynthesis_contDiff N c)
      hp (finiteSynthesis_periodic N c) hpp (finiteSynthesis_divergence_free N c hcs)
  have hskew := CRITICAL_ROUGH_TRANSPORT_SKEW (finiteSynthesis N c)
    (fderiv ℝ (finiteSynthesis N c)) (finiteSynthesis N b)
    (criticalPhysicalH1_smooth _ (finiteSynthesis_contDiff N c) (finiteSynthesis_periodic N c))
    hdiv (finiteSynthesis_contDiff N b) (finiteSynthesis_periodic N b)
  change criticalWeakTransport (finiteSynthesis N c) (finiteSynthesis N b) =
    -physicalFieldInner (finiteSynthesis N b) (convection (finiteSynthesis N c)) at hskew
  have hconv : physicalFieldInner (finiteSynthesis N b) (convection (finiteSynthesis N c)) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (b k i) * coefficientTransport N c k i).re := by
    rw [physicalFieldInner, integral_finiteSynthesis_pairing N b _
      (convection_continuous (finiteSynthesis_contDiff N c)),
      datumFourierCoeff_convection_finiteSynthesis N c hcsupp hcr]
  have htime : physicalFieldInner (finiteSynthesis N (galerkinRhs ν N c)) (finiteSynthesis N b) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (b k i) * galerkinRhs ν N c k i).re := by
    rw [critical_physicalFieldInner_comm]
    exact FINITE_PHYSICAL_BILINEAR_PARSEVAL N b (galerkinRhs ν N c) hbr
      (galerkinRhs_reality ν N c hcr)
  have hlap : physicalFieldInner (finiteSynthesis N c) (laplacian (finiteSynthesis N b)) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (laplacianCoefficient b k i) * c k i).re := by
    rw [critical_physicalFieldInner_comm, finiteSynthesis_laplacian]
    exact FINITE_PHYSICAL_BILINEAR_PARSEVAL N (laplacianCoefficient b) c
      (laplacianCoefficient_reality b hbr) hcr
  rw [htime, hlap, hskew, hconv]
  simp_rw [energy_galerkin_mode_pairing ν N c b hbs]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem energyGalerkin_finite_test_pairing
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (b : FourierCoeff) (hbr : SpectralReality b) (hbs : SpectralSolenoidal b)
    (t : ℝ) (ht : 0 ≤ t) :
    physicalFieldInner (timeDerivative g.velocity t) (finiteSynthesis N b) =
      ν * physicalFieldInner (g.velocity t) (laplacian (finiteSynthesis N b)) +
        criticalWeakTransport (g.velocity t) (finiteSynthesis N b) := by
  rw [g.timeDerivative_eq_finiteSynthesis t ht]
  exact ENERGY_FINITE_GALERKIN_WEAK_PAIRING ν N (g.coeff t) b
    (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht) hbr hbs

end
end QuasiFeffermanB
