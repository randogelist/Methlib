import SingularClosure.HighOrderAccumulation
import SingularClosure.HighOrderRhs
import SingularClosure.SobolevTimeModulus

/-!
# Actual uniform time moduli in every Sobolev order

AX6 controls the higher Galerkin energies. The proved nonlinear RHS estimate
then bounds the actual Sobolev-valued derivative, and the Hilbert-space
fundamental theorem of calculus gives a uniform time modulus.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

theorem AX6_UNIFORM_HIGH_ORDER_POINTWISE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState m t‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_HIGH_ORDER_ACCUMULATION hAX6 ν hν a ha T hT m
  refine ⟨B, hB, ?_⟩
  intro N hN g t ht
  have hi : 0 ≤ ∫ r in (0 : ℝ)..t, ‖g.sobolevState (m + 1) r‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => sq_nonneg _)
  have h := hb N hN g t ht
  nlinarith [mul_nonneg hν.le hi]

/-- Uniform actual RHS norm in every integral Sobolev order. -/
theorem AX6_UNIFORM_HIGH_ORDER_RHS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.rhsSobolev m t‖ ^ 2 ≤ B := by
  obtain ⟨B2, hB2, hb2⟩ := AX6_UNIFORM_HIGH_ORDER_POINTWISE hAX6 ν hν a ha T hT 2
  obtain ⟨B1, hB1, hb1⟩ := AX6_UNIFORM_HIGH_ORDER_POINTWISE hAX6 ν hν a ha T hT (m + 1)
  obtain ⟨B0, hB0, hb0⟩ := AX6_UNIFORM_HIGH_ORDER_POINTWISE hAX6 ν hν a ha T hT (m + 2)
  obtain ⟨C, hC, hrhs⟩ := GALERKIN_SOBOLEV_TIME_DERIVATIVE_BOUND m
  refine ⟨2 * ν ^ 2 * B0 + C * B2 * B1, by positivity, ?_⟩
  intro N hN g t ht
  have h := hrhs ν a N g t ht.1
  rw [g.sobolevState_derivWithin m t ht.1] at h
  have h' : ‖g.rhsSobolev m t‖ ^ 2 ≤
      2 * ν ^ 2 * ‖g.sobolevState (m + 2) t‖ ^ 2 +
        C * ‖g.sobolevState 2 t‖ ^ 2 * ‖g.sobolevState (m + 1) t‖ ^ 2 := by
    simpa only [highOrderEnergy_eq_sobolev_norm_sq, GalerkinSolution.sobolevState] using h
  have hv := mul_le_mul_of_nonneg_left (hb0 N hN g t ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ν))
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul (hb2 N hN g t ht) (hb1 N hN g t ht) (sq_nonneg _) hB2) hC.le
  nlinarith

theorem GalerkinSolution.sobolevState_time_modulus
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (m : ℕ) {s t T : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    ‖g.sobolevState m t - g.sobolevState m s‖ ^ 2 ≤
      (t - s) * (∫ r in (0 : ℝ)..T, ‖g.rhsSobolev m r‖ ^ 2) := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hrhs : ContinuousOn (g.rhsSobolev m) (Icc s t) :=
    (g.rhsSobolev_continuousOn m).mono (fun r hr => hs.trans hr.1)
  have hlocal :=
    intervalIntegral_norm_sq_le_length_mul_integral_norm_sq_banach hst hrhs
  rw [g.sobolevState_integral_rhs m hs hst] at hlocal
  have hfull : (∫ r in s..t, ‖g.rhsSobolev m r‖ ^ 2) ≤
      ∫ r in (0 : ℝ)..T, ‖g.rhsSobolev m r‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval hs hst htT
    · exact Filter.Eventually.of_forall fun r => sq_nonneg _
    · exact (((g.rhsSobolev_continuousOn m).mono
        (fun r hr => hr.1)).norm.pow 2).intervalIntegrable_of_Icc hT
  exact hlocal.trans (mul_le_mul_of_nonneg_left hfull (sub_nonneg.mpr hst))

/-- Uniform time equicontinuity of the actual Galerkin paths in every Sobolev order. -/
theorem AX6_UNIFORM_HIGH_ORDER_TIME_MODULUS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t - g.sobolevState m s‖ ^ 2 ≤ B * |t - s| := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_HIGH_ORDER_RHS hAX6 ν hν a ha T hT m
  refine ⟨T * B, mul_nonneg hT.le hB, ?_⟩
  intro N hN g s hs t ht
  have henergy : (∫ r in (0 : ℝ)..T, ‖g.rhsSobolev m r‖ ^ 2) ≤ T * B := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..T, B := by
        apply intervalIntegral.integral_mono_on hT.le
          ((((g.rhsSobolev_continuousOn m).mono
            (fun r hr => hr.1)).norm.pow 2).intervalIntegrable_of_Icc hT.le)
          intervalIntegrable_const
        exact hb N hN g
      _ = _ := by simp
  have hordered {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
      ‖g.sobolevState m v - g.sobolevState m u‖ ^ 2 ≤ (v - u) * (T * B) :=
    (g.sobolevState_time_modulus m hu huv hvT).trans
      (mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr huv))
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using
      hordered hs.1 hst ht.2
  · calc
      _ = ‖g.sobolevState m s - g.sobolevState m t‖ ^ 2 := by rw [norm_sub_rev]
      _ ≤ (s - t) * (T * B) := hordered ht.1 hts hs.2
      _ = (T * B) * |t - s| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, mul_comm]

end

end SingularClosure
