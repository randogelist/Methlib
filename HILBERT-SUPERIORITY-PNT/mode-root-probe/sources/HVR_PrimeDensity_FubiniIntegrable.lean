import HVR_PrimeDensity_FubiniBridge
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Filter MeasureTheory HVRPrimeZetaSplit HVRPrimeDensityLaplace
open HVRPrimeDensityFubiniBridge

/-!
Candidate removal of the product-integrability hypothesis for the actual
Abel-smoothed prime error. The frequency test is assumed integrable and the
Abel parameter positive; no kernel positivity or Fourier support is claimed.
The candidate requires the user's cached external Lean build and axiom audit.
No Lean was executed locally.
-/
namespace HVRPrimeDensityFubiniIntegrable

/-- The actual damped prime error is integrable for positive damping. -/
theorem dampedError_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (dampedError a) (Set.Ioi 0) volume := by
  have hs : 1 < 1 + a := by linarith
  have hpoint : zetaPoint (1 + a) 0 - 1 = (a : ℂ) := by
    simp only [zetaPoint, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_zero, zero_mul, add_zero]
    ring
  change IntegrableOn (fun u : ℝ =>
    ((HVRPrimeLogDensity.logPrimeDensity u : ℂ) - 1) *
      Complex.exp (-(a : ℂ) * (u : ℂ))) (Set.Ioi 0) volume
  rw [← hpoint]
  exact primeDensity_integrable (1 + a) 0 hs

/-- The mixed Fubini integrand is absolutely integrable, since its oscillatory
factor has modulus one and the remaining factors are separately integrable. -/
theorem mixed_integrable (ψ : ℝ → ℂ) (a x : ℝ)
    (hψ : Integrable ψ volume) (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  have hbase : Integrable (fun p : ℝ × ℝ => dampedError a p.1 * ψ p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    (dampedError_integrable a ha).mul_prod hψ
  have hphase : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((p.2 : ℂ) * Complex.I * ((x - p.1 : ℝ) : ℂ))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
    have heq : (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2) =
        (fun p : ℝ × ℝ => dampedError a p.1 * ψ p.2) *
          (fun p : ℝ × ℝ => Complex.exp
            ((p.2 : ℂ) * Complex.I * ((x - p.1 : ℝ) : ℂ))) := by
      funext p
      simp only [Pi.mul_apply, mixed, mul_assoc]
    rw [heq]
    exact hbase.aestronglyMeasurable.mul hphase.measurable.aestronglyMeasurable
  apply Integrable.mono' hbase.norm hmeas
  apply Filter.Eventually.of_forall
  intro p
  have hphase_norm :
      ‖Complex.exp ((p.2 : ℂ) * Complex.I * ((x - p.1 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  simp only [mixed, norm_mul, hphase_norm, mul_one, le_refl]

/-- The Fubini identity with its product-integrability input discharged. -/
theorem abel_smoothing_eq_frequency_integral_of_integrable
    (ψ : ℝ → ℂ) (a x : ℝ) (hψ : Integrable ψ volume) (ha : 0 < a) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) :=
  abel_smoothing_eq_frequency_integral ψ a x (mixed_integrable ψ a x hψ ha)

end HVRPrimeDensityFubiniIntegrable
