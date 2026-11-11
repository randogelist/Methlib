import SingularClosure.CriticalSpacesEmbedding
import SingularClosure.CriticalGalerkinTrajectory

/-! Quantitative spatial tails in the actual half-order Fourier spaces.

Dropping one half derivative gives N^(-1) for the squared tail norm.
Consequently the H^(3/2) time-energy controls the discarded H1 time-energy.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology Interval

namespace SingularClosure

noncomputable section

theorem criticalCoeff_sub (q : ℤ) (c d : CriticalSobolev q) :
    criticalCoeff q (c - d) = criticalCoeff q c - criticalCoeff q d := rfl

theorem criticalFrequencyWeight_ge_cutoff {N : ℕ} {k : Frequency}
    (hk : k ∉ sobolevCutoffModes N) : (N : ℝ) ≤ criticalFrequencyWeight k := by
  have hk0 : k ≠ 0 := by
    intro h
    apply hk
    simp [sobolevCutoffModes, h]
  have hfreq : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  have hsq : (N : ℝ) ^ 2 < (galerkinFreqSq k : ℝ) := by
    exact_mod_cast freqSq_gt_of_not_mem_sobolevCutoff hk
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hweight := criticalFrequencyWeight_sq_of_ne_zero k hk0
  change criticalFrequencyWeight k ^ 2 =
    (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) at hweight
  have hpos := criticalFrequencyWeight_pos k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_right hpi hfreq]

theorem criticalWeightedCoeff_add_one_norm (q : ℤ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖criticalWeightedCoeff (q + 1) c ki‖ =
      criticalHalfWeight ki.1 * ‖criticalWeightedCoeff q c ki‖ := by
  rw [criticalWeightedCoeff_norm, criticalWeightedCoeff_norm,
    zpow_add₀ (criticalHalfWeight_pos ki.1).ne', zpow_one]
  ring

theorem critical_tail_half_weight_factor (N : ℕ) (hN : 0 < N)
    {k : Frequency} (hk : k ∉ sobolevCutoffModes N) :
    1 ≤ Real.sqrt (N : ℝ)⁻¹ * criticalHalfWeight k := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNreal.le
  have hw := criticalFrequencyWeight_ge_cutoff hk
  have hfactor : 1 ≤ (N : ℝ)⁻¹ * criticalFrequencyWeight k := by
    calc
      1 = (N : ℝ)⁻¹ * (N : ℝ) := (inv_mul_cancel₀ hNreal.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hw hinv
  have hsquare : (Real.sqrt (N : ℝ)⁻¹ * criticalHalfWeight k) ^ 2 =
      (N : ℝ)⁻¹ * criticalFrequencyWeight k := by
    rw [mul_pow, Real.sq_sqrt hinv, criticalHalfWeight_sq]
  have hnonneg : 0 ≤ Real.sqrt (N : ℝ)⁻¹ * criticalHalfWeight k :=
    mul_nonneg (Real.sqrt_nonneg _) (criticalHalfWeight_pos k).le
  nlinarith

/-- Actual one-half-order cutoff tail, without a separate compactness hypothesis. -/
theorem criticalSobolevLower_tail (q : ℤ) (N : ℕ) (hN : 0 < N)
    (c : CriticalSobolev (q + 1)) :
    ‖criticalSobolevLower q (q + 1) (by omega) c -
      criticalSobolevCutoff q N (criticalSobolevLower q (q + 1) (by omega) c)‖ ≤
      Real.sqrt (N : ℝ)⁻¹ * ‖c‖ := by
  let v := criticalSobolevLower q (q + 1) (by omega) c
  calc
    _ = ‖criticalSobolevRepr q (v - criticalSobolevCutoff q N v)‖ :=
      ((criticalSobolevRepr q).norm_map _).symm
    _ ≤ ‖Real.sqrt (N : ℝ)⁻¹ • criticalSobolevRepr (q + 1) c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [criticalSobolevRepr_apply, criticalCoeff_sub,
        criticalSobolevCutoff_coeff]
      change ‖criticalWeightedCoeff q
          (fun k i => criticalCoeff q v k i -
            if k ∈ sobolevCutoffModes N then criticalCoeff q v k i else 0) ki‖ ≤
        ‖Real.sqrt (N : ℝ)⁻¹ • criticalWeightedCoeff (q + 1) (criticalCoeff (q + 1) c) ki‖
      by_cases hk : ki.1 ∈ sobolevCutoffModes N
      · simp only [criticalWeightedCoeff, if_pos hk, sub_self, mul_zero, norm_zero]
        exact norm_nonneg _
      · have hcoeff : criticalCoeff q v = criticalCoeff (q + 1) c :=
          criticalSobolevLower_coeff q (q + 1) (by omega) c
        simp only [criticalWeightedCoeff, if_neg hk, sub_zero, hcoeff]
        change ‖criticalWeightedCoeff q (criticalCoeff (q + 1) c) ki‖ ≤
          ‖Real.sqrt (N : ℝ)⁻¹ • criticalWeightedCoeff (q + 1) (criticalCoeff (q + 1) c) ki‖
        rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          criticalWeightedCoeff_add_one_norm]
        have hfactor := critical_tail_half_weight_factor N hN hk
        calc
          _ = 1 * ‖criticalWeightedCoeff q (criticalCoeff (q + 1) c) ki‖ := (one_mul _).symm
          _ ≤ (Real.sqrt (N : ℝ)⁻¹ * criticalHalfWeight ki.1) *
              ‖criticalWeightedCoeff q (criticalCoeff (q + 1) c) ki‖ :=
            mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
          _ = _ := mul_assoc _ _ _
    _ = _ := by
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        (criticalSobolevRepr (q + 1)).norm_map]

theorem criticalSobolevLower_tail_sq (q : ℤ) (N : ℕ) (hN : 0 < N)
    (c : CriticalSobolev (q + 1)) :
    ‖criticalSobolevLower q (q + 1) (by omega) c -
      criticalSobolevCutoff q N (criticalSobolevLower q (q + 1) (by omega) c)‖ ^ 2 ≤
      (N : ℝ)⁻¹ * ‖c‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (criticalSobolevLower_tail q N hN c) 2
  simpa only [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg N))] using h

/-- The critical state bound controls the actual H0 spatial tail. -/
theorem criticalToTorusH0_tail_sq (N : ℕ) (hN : 0 < N) (c : CriticalSobolev 1) :
    ‖criticalToTorusH0 1 (by norm_num) c -
      torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) c)‖ ^ 2 ≤
      (N : ℝ)⁻¹ * ‖c‖ ^ 2 := by
  let v : CriticalSobolev 0 := criticalSobolevLower 0 1 (by norm_num) c
  have heq : criticalToTorusH0 1 (by norm_num) c -
      torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) c) =
      criticalH0Equiv (v - criticalSobolevCutoff 0 N v) := by
    apply Subtype.ext
    funext k i
    change (criticalToTorusH0 1 (by norm_num) c).val k i -
      (torusSobolevCutoff 0 N (criticalToTorusH0 1 (by norm_num) c)).val k i = _
    rw [torusSobolevCutoff_coeff, criticalToTorusH0_coeff, criticalH0Equiv_coeff,
      criticalCoeff_sub, criticalSobolevCutoff_coeff]
    simp only [v, criticalSobolevLower_coeff, Pi.sub_apply]
  rw [heq, criticalH0Equiv.norm_map]
  exact criticalSobolevLower_tail_sq 0 N hN c

/-- Comparison of an H1 vector and the same coefficients in homogeneous H1. -/
theorem torusH1_norm_le_two_criticalH1
    (u : TorusSobolev 1) (v : CriticalSobolev 2) (hcoeff : u.val = criticalCoeff 2 v) :
    ‖u‖ ≤ 2 * ‖v‖ := by
  calc
    _ = ‖torusSobolevRepr 1 u‖ := ((torusSobolevRepr 1).norm_map u).symm
    _ ≤ ‖(2 : ℂ) • criticalSobolevRepr 2 v‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [torusSobolevRepr_apply, criticalSobolevRepr_apply, hcoeff]
      change ‖(torusSobolevWeight ki.1 : ℂ) * criticalCoeff 2 v ki.1 ki.2‖ ≤
        ‖(2 : ℂ) * criticalWeightedCoeff 2 (criticalCoeff 2 v) ki‖
      rw [norm_mul, norm_mul, criticalWeightedCoeff_norm]
      simp only [norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (torusSobolevWeight_pos ki.1), zpow_ofNat,
        criticalHalfWeight_sq]
      have h := mul_le_mul_of_nonneg_right
        (torusSobolevWeight_le_two_criticalFrequencyWeight ki.1)
        (norm_nonneg (criticalCoeff 2 v ki.1 ki.2))
      simpa only [mul_assoc] using h
    _ = _ := by rw [norm_smul, norm_ofNat, (criticalSobolevRepr 2).norm_map]

/-- The actual inhomogeneous H1 tail gains N^(-1) from the H^(3/2) energy. -/
theorem criticalToTorusH1_tail_sq (N : ℕ) (hN : 0 < N) (c : CriticalSobolev 3) :
    ‖criticalToTorusH1 c - torusSobolevCutoff 1 N (criticalToTorusH1 c)‖ ^ 2 ≤
      4 * (N : ℝ)⁻¹ * ‖c‖ ^ 2 := by
  let v : CriticalSobolev 2 := criticalSobolevLower 2 3 (by norm_num) c
  have hcoeff : (criticalToTorusH1 c - torusSobolevCutoff 1 N (criticalToTorusH1 c)).val =
      criticalCoeff 2 (v - criticalSobolevCutoff 2 N v) := by
    funext k i
    change (criticalToTorusH1 c).val k i -
      (torusSobolevCutoff 1 N (criticalToTorusH1 c)).val k i = _
    rw [torusSobolevCutoff_coeff, criticalToTorusH1_coeff,
      criticalCoeff_sub, criticalSobolevCutoff_coeff]
    simp only [v, criticalSobolevLower_coeff, Pi.sub_apply]
  have hnorm := torusH1_norm_le_two_criticalH1 _ _ hcoeff
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have htail := criticalSobolevLower_tail_sq 2 N hN c
  change ‖v - criticalSobolevCutoff 2 N v‖ ^ 2 ≤ (N : ℝ)⁻¹ * ‖c‖ ^ 2 at htail
  nlinarith

/-- The H^(3/2) time budget controls discarded H1 modes, including near zero time. -/
theorem criticalToTorusH1_time_tail_sq
    (v : ℝ → CriticalSobolev 3) (T B : ℝ) (hT : 0 ≤ T)
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (hbudget : (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤ B)
    (N : ℕ) (hN : 0 < N) :
    (∫ t in (0 : ℝ)..T,
      ‖criticalToTorusH1 (v t) - torusSobolevCutoff 1 N (criticalToTorusH1 (v t))‖ ^ 2) ≤
      4 * (N : ℝ)⁻¹ * B := by
  have hu := criticalToTorusH1.continuous.comp_continuousOn hv
  have hcut := (torusSobolevCutoff 1 N).continuous.comp_continuousOn hu
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, 4 * (N : ℝ)⁻¹ * ‖v t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hT
        (((hu.sub hcut).norm.pow 2).intervalIntegrable_of_Icc hT)
        (((hv.norm.pow 2).const_mul (4 * (N : ℝ)⁻¹)).intervalIntegrable_of_Icc hT)
      intro t ht
      exact criticalToTorusH1_tail_sq N hN (v t)
    _ = 4 * (N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

end

end SingularClosure
