import HVR_PrimeDensity_Laplace
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory HVRPrimeLogDensity HVRPrimeDensityLaplace

/-! Candidate exact Fubini bridge for the actual prime-count error.
The product-integrability premise is explicit and remains to be discharged.
The frequency test defines a kernel directly; this module does not prove
positivity, normalization, compact Fourier support, Fourier decay, or PNT.
No local Lean execution was performed. -/
namespace HVRPrimeDensityFubiniBridge

/-- A kernel defined by an ordinary-frequency inverse integral. -/
def kernel (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, ψ t * Complex.exp ((t : ℂ) * Complex.I * (y : ℂ))

/-- The actual prime-count error with Abel damping. -/
def dampedError (a u : ℝ) : ℂ :=
  ((logPrimeDensity u : ℂ) - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))

/-- The mixed integrand whose product integrability justifies Fubini. -/
def mixed (ψ : ℝ → ℂ) (a x u t : ℝ) : ℂ :=
  dampedError a u *
    (ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))

/-- Algebraic separation of spatial and Laplace-frequency factors. -/
theorem mixed_factorization (ψ : ℝ → ℂ) (a x u t : ℝ) :
    mixed ψ a x u t =
      (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        (((logPrimeDensity u : ℂ) - 1) *
          Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) := by
  have hexp : Complex.exp (-(a : ℂ) * (u : ℂ)) *
      Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)) =
      Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) *
        Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold mixed dampedError
  calc
    (((logPrimeDensity u : ℂ) - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))) *
        (ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ))) =
      ψ t * (((logPrimeDensity u : ℂ) - 1) *
        (Complex.exp (-(a : ℂ) * (u : ℂ)) *
          Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))) := by ring
    _ = _ := by rw [hexp]; ring

/- The indicator induction below adapts the finite-measure indicator argument of
Mathlib/MeasureTheory/Integral/Prod.lean (Floris van Doorn, 2020, Apache 2.0).
Its closure step uses continuity of the iterated integral on complex L¹. -/
section SectionIntegral
open Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure TopologicalSpace
open Filter hiding prod_eq map
open scoped Topology ENNReal MeasureTheory

/-- Reconstruct one order of complex integration on the real product space
from finite indicators, additivity, L¹ continuity, and a.e. congruence. -/
theorem complex_integral_from_sections (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (f : ℝ × ℝ → ℂ) (hf : Integrable f (μ.prod ν)) :
    (∫ p, f p ∂μ.prod ν) = ∫ u, ∫ t, f (u, t) ∂ν ∂μ := by
  revert f
  apply Integrable.induction
  · intro c s hs hfinite
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs hfinite.ne)]
    rw [Measure.prod_apply hs]
  · rintro f g - if_ ig hf hg
    simp_rw [integral_add' if_ ig, integral_integral_add' if_ ig, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf
    convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with u hu using integral_congr_ae (ae_eq_symm hu)

/-- Exchange the mixed kernel's order through its product integral and the
measure-preserving coordinate exchange. -/
theorem mixed_integral_exchange (ψ : ℝ → ℂ) (a x : ℝ)
    (hpair : Integrable (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ, mixed ψ a x u t) =
      ∫ t : ℝ, ∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let ν : Measure ℝ := volume
  let f : ℝ × ℝ → ℂ := fun p => mixed ψ a x p.1 p.2
  have hf : Integrable f (μ.prod ν) := hpair
  have hflip : (∫ p : ℝ × ℝ, f p.swap ∂ν.prod μ) = ∫ p, f p ∂μ.prod ν :=
    measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _
  exact (complex_integral_from_sections μ ν f hf).symm.trans
    (hflip.symm.trans (complex_integral_from_sections ν μ (fun p => f p.swap) hf.swap))

end SectionIntegral

/-- Fubini identifies the Abel-smoothed actual prime error with the integral
of its actual Laplace transform. Product integrability is an explicit input. -/
theorem abel_smoothing_eq_frequency_integral (ψ : ℝ → ℂ) (a x : ℝ)
    (hpair : Integrable (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  calc
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
        ∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ, mixed ψ a x u t := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold kernel mixed
      rw [integral_const_mul]
    _ = ∫ t : ℝ, ∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t := by
      exact mixed_integral_exchange ψ a x hpair
    _ = ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp_rw [mixed_factorization]
      rw [integral_const_mul]
      rfl

end HVRPrimeDensityFubiniBridge
