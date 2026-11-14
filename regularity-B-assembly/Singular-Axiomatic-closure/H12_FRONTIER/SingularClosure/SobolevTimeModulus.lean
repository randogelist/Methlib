import SingularClosure.SobolevTrajectoryCalculus
import SingularClosure.GalerkinCoefficientCompactness

/-!
# The actual Sobolev H0 time modulus

The fundamental theorem of calculus is applied to the literal Sobolev-valued
Galerkin path. Its derivative is the already identified finite Galerkin vector
field. Integral Cauchy--Schwarz and the physical time-derivative bound give a
cutoff-independent squared one-half-Hölder modulus under AX6.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

theorem intervalIntegral_norm_sq_le_length_mul_integral_norm_sq_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    ‖∫ r in a..b, f r‖ ^ 2 ≤ (b - a) * (∫ r in a..b, ‖f r‖ ^ 2) := by
  calc
    _ ≤ (∫ r in a..b, ‖f r‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (intervalIntegral.norm_integral_le_integral_norm hab) 2
    _ ≤ _ := intervalIntegral_sq_le_length_mul_integral_sq hab hf.norm

theorem GalerkinSolution.sobolevState_integral_rhs
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, g.rhsSobolev q r) = g.sobolevState q t - g.sobolevState q s := by
  have hcont : ContinuousOn (g.sobolevState q) (Icc s t) :=
    (g.sobolevState_continuousOn q).mono (fun r hr => hs.trans hr.1)
  have hrhs : ContinuousOn (g.rhsSobolev q) (Icc s t) :=
    (g.rhsSobolev_continuousOn q).mono (fun r hr => hs.trans hr.1)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont
    _ (hrhs.intervalIntegrable_of_Icc hst)
  intro r hr
  have hrpos : 0 < r := hs.trans_lt hr.1
  exact (g.sobolevState_hasDerivWithinAt q r hrpos.le).hasDerivAt
    (Ici_mem_nhds hrpos)

/-- The physical time-derivative energy controls the actual Hilbert-space increment. -/
theorem GalerkinSolution.sobolevState_H0_time_modulus
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {s t T : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖g.sobolevState 0 t - g.sobolevState 0 s‖ ^ 2 ≤
      (t - s) * (∫ r in (0 : ℝ)..T,
        ∫ x in unitCube, ‖timeDerivative g.velocity r x‖ ^ 2) := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hlen : 0 ≤ t - s := sub_nonneg.mpr hst
  have hrhs : ContinuousOn (g.rhsSobolev 0) (Icc s t) :=
    (g.rhsSobolev_continuousOn 0).mono (fun r hr => hs.trans hr.1)
  have hlocal :=
    intervalIntegral_norm_sq_le_length_mul_integral_norm_sq_banach hst hrhs
  rw [g.sobolevState_integral_rhs 0 hs hst] at hlocal
  have hphysical : (∫ r in s..t, ‖g.rhsSobolev 0 r‖ ^ 2) =
      ∫ r in s..t, ∫ x in unitCube, ‖timeDerivative g.velocity r x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hm : r ∈ Icc s t := by simpa only [uIcc_of_le hst] using hr
    exact g.rhsSobolev_H0_physical_norm_sq r (hs.trans hm.1)
  rw [hphysical] at hlocal
  have hfull : (∫ r in s..t, ∫ x in unitCube,
      ‖timeDerivative g.velocity r x‖ ^ 2) ≤
      ∫ r in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity r x‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval hs hst htT
    · exact Filter.Eventually.of_forall fun r => integral_nonneg (fun x => sq_nonneg _)
    · exact g.timeDerivative_energy_intervalIntegrable hT
  exact hlocal.trans (mul_le_mul_of_nonneg_left hfull hlen)

/-- AX6 yields the uniform H0 time modulus without a compactness or regularity premise. -/
theorem AX6_UNIFORM_H0_TIME_MODULUS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState 0 t - g.sobolevState 0 s‖ ^ 2 ≤ B * |t - s| := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_TIME_DERIVATIVE_BOUND hAX6 ν hν a ha T hT
  refine ⟨B, hB, ?_⟩
  intro N hN g s hs t ht
  have hordered {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
      ‖g.sobolevState 0 v - g.sobolevState 0 u‖ ^ 2 ≤ (v - u) * B :=
    (g.sobolevState_H0_time_modulus hu huv hvT).trans
      (mul_le_mul_of_nonneg_left (hb N hN g) (sub_nonneg.mpr huv))
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using
      hordered hs.1 hst ht.2
  · calc
      _ = ‖g.sobolevState 0 s - g.sobolevState 0 t‖ ^ 2 := by
        rw [norm_sub_rev]
      _ ≤ (s - t) * B := hordered ht.1 hts hs.2
      _ = B * |t - s| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, mul_comm]

end

end SingularClosure
