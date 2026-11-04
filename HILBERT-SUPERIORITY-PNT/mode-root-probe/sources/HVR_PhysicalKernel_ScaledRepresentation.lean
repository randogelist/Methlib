import HVR_PhysicalKernel_SpectralIdentity
import HVR_PhysicalKernel_ScaledSpectrum
import HVR_PhysicalKernel_ScaledTranslate
import HVR_PrimeDensity_FubiniBridge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory HVRPhysicalKernelCandidate HVRPhysicalKernelScaledTranslate
open HVRPhysicalKernelScaledSpectrum HVRPhysicalKernelSpectralIdentity
open HVRSpectralCorrelationCompact HVRPrimeDensityFubiniBridge
open HVRSpectralSeedCorrelation

/-!
Candidate identification of the ordinary-frequency inverse kernel from the
explicit scaled correlation with the actual normalized scaled physical
kernel. The 2*pi convention and affine change of variables are explicit.
No Lean run was performed locally. The pinned external compiler and a named
axiom audit must verify this proof. No PNT claim is made here.
-/
namespace HVRPhysicalKernelScaledRepresentation

/-- The same complex-valued inverse kernel used by the audited Abel bridge
is the real nonnegative scaled physical kernel, embedded in the complex field. -/
theorem kernel_scaledSpectrum_eq_scaledTranslate
    (w : ℝ) (hw : 0 < w) (N c x : ℝ) (hN : 0 < N) :
    kernel (scaledSpectrum w hw N c) x =
      (scaledTranslate w hw N c x : ℂ) := by
  let A : ℝ := 2 * Real.pi * N
  let B : ℝ := 2 * Real.pi * mass w hw
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; exact mul_pos (by positivity) (mass_pos w hw)
  let f : ℝ → ℂ := fun u =>
    Complex.exp (((2 * Real.pi * (u * (N * (x - c))) : ℝ) : ℂ) * Complex.I) *
      complexCorrelation w hw u
  have hfourier : (∫ u : ℝ, f u) = (rawKernel w hw (N * (x - c)) : ℂ) := by
    rw [← fourierInv_correlation_eq_rawKernel]
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul, f]
  have hscale : (∫ t : ℝ, f (A⁻¹ * t)) = (A : ℂ) * ∫ u : ℝ, f u := by
    have hh := Measure.integral_comp_mul_left f A⁻¹
    simpa only [inv_inv, abs_of_pos hA, Complex.real_smul] using hh
  have hdiv (t : ℝ) : t / (2 * Real.pi * N) = A⁻¹ * t := by
    dsimp [A]
    rw [div_eq_mul_inv, mul_comm]
  have hphase_real (t : ℝ) :
      2 * Real.pi * ((A⁻¹ * t) * (N * (x - c))) = t * (x - c) := by
    dsimp [A]
    field_simp [ne_of_gt Real.pi_pos, ne_of_gt hN] <;> ring
  have hphase (t : ℝ) :
      Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ)) *
        Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) =
      Complex.exp (((2 * Real.pi * ((A⁻¹ * t) * (N * (x - c))) : ℝ) : ℂ) * Complex.I) := by
    rw [hphase_real, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hkernel : kernel (scaledSpectrum w hw N c) x =
      (B : ℂ)⁻¹ * ∫ t : ℝ, f (A⁻¹ * t) := by
    unfold kernel
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [scaledSpectrum, f, complexCorrelation, Function.comp_apply, hdiv]
    change ((B : ℂ)⁻¹ * Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ)) *
      (correlation w hw (A⁻¹ * t) : ℂ)) *
        Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) = _
    calc
      _ = (B : ℂ)⁻¹ * ((correlation w hw (A⁻¹ * t) : ℂ) *
        (Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ)) *
          Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))) := by ring
      _ = _ := by rw [hphase]; ring
  rw [hkernel, hscale, hfourier]
  change (B : ℂ)⁻¹ * ((A : ℂ) * (rawKernel w hw (N * (x - c)) : ℂ)) =
    ((N * (rawKernel w hw (N * (x - c)) / mass w hw) : ℝ) : ℂ)
  dsimp [A, B]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Real.pi_pos)
  have hm : (mass w hw : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (mass_pos w hw))
  field_simp [hpi, hm] <;> ring

end HVRPhysicalKernelScaledRepresentation
