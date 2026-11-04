import HVROneDimensionalCompactDecay
import HVRAnalyticPhaseBasics
import HVROrdinarySeed
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv

/-! Candidate direct 1D phase-integral decay for the actual compact HVR seed.
It chooses a bounded interval containing both seed and derivative support,
then applies finite-interval integration by parts. No local Lean run has been
performed; external compilation, axiom auditing, and a transitive swap trace
are required. -/

noncomputable section
open Filter MeasureTheory
open HVROrdinarySeed HVRAnalyticPhaseBasics

namespace HVRStandaloneSeedIntervalDecay

theorem seed_deriv_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (deriv (complexSeed w hw)) := by
  exact ((complexSeed_smooth w hw).continuous_deriv (by simp)).integrable_of_hasCompactSupport
    (complexSeed_compact w hw).deriv

theorem phase_hasDerivAt (ξ t : ℝ) :
    HasDerivAt (fun s : ℝ => phase s ξ) ((-(ξ : ℂ) * Complex.I) * phase t ξ) t := by
  let c : ℂ := -(ξ : ℂ) * Complex.I
  have heq : (fun s : ℝ => Complex.exp ((s : ℂ) * c)) =
      (fun s : ℝ => phase s ξ) := by
    funext s
    unfold phase c
    congr 1
    push_cast
    ring
  have hd := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const c).cexp
  change HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c)) _ t at hd
  rw [heq] at hd
  have heval : Complex.exp ((t : ℂ) * c) = phase t ξ := congrFun heq t
  rw [heval] at hd
  convert hd using 1 <;> simp [c, Complex.ofRealCLM_apply] <;> ring

/-- First-derivative bound for the direct ordinary phase transform. -/
theorem seed_phase_first_derivative_bound (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    |ξ| * ‖∫ t : ℝ, complexSeed w hw t * phase t ξ‖ ≤
      ∫ t : ℝ, ‖deriv (complexSeed w hw) t‖ := by
  obtain ⟨Rf, hRf, hfzero⟩ := (complexSeed_compact w hw).exists_pos_le_norm
  obtain ⟨Rd, hRd, hd_zero⟩ := (complexSeed_compact w hw).deriv.exists_pos_le_norm
  let R : ℝ := max Rf Rd + 1
  have hRfR : Rf ≤ R := by dsimp [R]; linarith [le_max_left Rf Rd]
  have hRdR : Rd ≤ R := by dsimp [R]; linarith [le_max_right Rf Rd]
  have hR : 0 < R := lt_of_lt_of_le hRf hRfR
  have hzero (t : ℝ) (ht : R ≤ |t|) : complexSeed w hw t = 0 := by
    apply hfzero t
    simpa only [Real.norm_eq_abs] using le_trans hRfR ht
  have hdzero (t : ℝ) (ht : R ≤ |t|) : deriv (complexSeed w hw) t = 0 := by
    apply hd_zero t
    simpa only [Real.norm_eq_abs] using le_trans hRdR ht
  have hnotband (t : ℝ) (ht : t ∉ Set.Ioc (-R) R) : R ≤ |t| := by
    by_contra hn
    have habs : |t| < R := lt_of_not_ge hn
    exact ht ⟨(abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  have hminus : complexSeed w hw (-R) = 0 := by
    apply hzero (-R)
    simp [abs_of_pos hR]
  have hplus : complexSeed w hw R = 0 := by
    apply hzero R
    simp [abs_of_pos hR]
  have hf'cont : Continuous (deriv (complexSeed w hw)) :=
    (complexSeed_smooth w hw).continuous_deriv (by simp)
  have hgcont : Continuous (fun t : ℝ => phase t ξ) := by
    unfold phase
    fun_prop
  have h := HVROneDimensionalCompactDecay.phase_integral_derivative_bound
    (-R) R (by linarith) (complexSeed w hw) (deriv (complexSeed w hw))
    (fun t : ℝ => phase t ξ) (-(ξ : ℂ) * Complex.I)
    (fun t => ((complexSeed_smooth w hw).differentiable (by simp) t).hasDerivAt)
    (fun t => phase_hasDerivAt ξ t) hf'cont hgcont hminus hplus
    (fun t ht => hzero t (hnotband t ht))
    (fun t ht => hdzero t (hnotband t ht))
    (seed_deriv_integrable w hw)
    (fun t => by simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im])
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] using h

end HVRStandaloneSeedIntervalDecay
