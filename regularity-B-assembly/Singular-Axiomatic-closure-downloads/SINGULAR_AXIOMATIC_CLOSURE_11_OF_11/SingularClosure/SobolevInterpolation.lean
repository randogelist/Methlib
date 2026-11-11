import SingularClosure.SobolevTimeModulus

/-!
# Actual weighted Fourier interpolation and its time-integral consequence

The H1 squared norm is the real part of the Hilbert inner product between
the unweighted and twice-weighted coefficient sequences. Cauchy--Schwarz
therefore gives H1² ≤ H0 H2. The time-integral comparison below uses only
literal norms of continuous H2-valued curves.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

/-- The exact H1 interpolation inequality in the actual weighted coefficient spaces. -/
theorem torusSobolev_H1_interpolation (c : TorusSobolev 2) :
    ‖torusSobolevInclusion 1 c‖ ^ 2 ≤
      ‖torusSobolevInclusion 0 (torusSobolevInclusion 1 c)‖ * ‖c‖ := by
  have hinner :
      inner ℂ (torusSobolevRepr 1 (torusSobolevInclusion 1 c))
        (torusSobolevRepr 1 (torusSobolevInclusion 1 c)) =
      inner ℂ (torusSobolevRepr 0
        (torusSobolevInclusion 0 (torusSobolevInclusion 1 c)))
        (torusSobolevRepr 2 c) := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro ki
    simp only [torusSobolevRepr_apply, torusSobolevInclusion_coeff,
      pow_zero, pow_one, one_mul, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal]
    ring
  calc
    _ = RCLike.re (inner ℂ (torusSobolevRepr 1 (torusSobolevInclusion 1 c))
        (torusSobolevRepr 1 (torusSobolevInclusion 1 c))) := by
      rw [inner_self_eq_norm_sq, (torusSobolevRepr 1).norm_map]
    _ = RCLike.re (inner ℂ (torusSobolevRepr 0
        (torusSobolevInclusion 0 (torusSobolevInclusion 1 c)))
        (torusSobolevRepr 2 c)) := congrArg (RCLike.re : ℂ → ℝ) hinner
    _ ≤ ‖torusSobolevRepr 0
        (torusSobolevInclusion 0 (torusSobolevInclusion 1 c))‖ *
        ‖torusSobolevRepr 2 c‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ = _ := by rw [(torusSobolevRepr 0).norm_map, (torusSobolevRepr 2).norm_map]

theorem torusSobolev_H1_sub_interpolation (c d : TorusSobolev 2) :
    ‖torusSobolevInclusion 1 c - torusSobolevInclusion 1 d‖ ^ 2 ≤
      ‖torusSobolevInclusion 0 (torusSobolevInclusion 1 c) -
        torusSobolevInclusion 0 (torusSobolevInclusion 1 d)‖ * ‖c - d‖ := by
  simpa only [map_sub] using torusSobolev_H1_interpolation (c - d)

/-- Uniform H0 size and the actual H2 time energy control the H1 time energy. -/
theorem torusSobolev_H1_time_interpolation
    (v : ℝ → TorusSobolev 2) (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (h0 : ∀ t ∈ Icc (0 : ℝ) T,
      ‖torusSobolevInclusion 0 (torusSobolevInclusion 1 (v t))‖ ≤ ε) :
    (∫ t in (0 : ℝ)..T, ‖torusSobolevInclusion 1 (v t)‖ ^ 2) ^ 2 ≤
      ε ^ 2 * T * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) := by
  have hv1 : ContinuousOn (fun t => torusSobolevInclusion 1 (v t)) (Icc (0 : ℝ) T) :=
    (torusSobolevInclusion 1).continuous.comp_continuousOn hv
  have hcompare : (∫ t in (0 : ℝ)..T, ‖torusSobolevInclusion 1 (v t)‖ ^ 2) ≤
      ε * (∫ t in (0 : ℝ)..T, ‖v t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT
      ((hv1.norm.pow 2).intervalIntegrable_of_Icc hT)
      ((continuousOn_const.mul hv.norm).intervalIntegrable_of_Icc hT)
    intro t ht
    exact (torusSobolev_H1_interpolation (v t)).trans
      (mul_le_mul_of_nonneg_right (h0 t ht) (norm_nonneg _))
  have hn : 0 ≤ ∫ t in (0 : ℝ)..T, ‖torusSobolevInclusion 1 (v t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg _)
  have hcs := intervalIntegral_sq_le_length_mul_integral_sq hT hv.norm
  simp only [sub_zero] at hcs
  calc
    _ ≤ (ε * (∫ t in (0 : ℝ)..T, ‖v t‖)) ^ 2 :=
      pow_le_pow_left₀ hn hcompare 2
    _ = ε ^ 2 * (∫ t in (0 : ℝ)..T, ‖v t‖) ^ 2 := mul_pow _ _ _
    _ ≤ ε ^ 2 * (T * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg ε)
    _ = _ := by ring

theorem torusSobolev_H1_time_interpolation_of_energy_bound
    (v : ℝ → TorusSobolev 2) (T ε M : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (h0 : ∀ t ∈ Icc (0 : ℝ) T,
      ‖torusSobolevInclusion 0 (torusSobolevInclusion 1 (v t))‖ ≤ ε)
    (h2 : (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤ M) :
    (∫ t in (0 : ℝ)..T, ‖torusSobolevInclusion 1 (v t)‖ ^ 2) ^ 2 ≤
      ε ^ 2 * T * M :=
  (torusSobolev_H1_time_interpolation v T ε hT hε hv h0).trans
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg ε) hT))

/-- A concrete difference estimate for two continuous H2 curves. -/
theorem torusSobolev_H1_time_difference_bound
    (v w : ℝ → TorusSobolev 2) (T ε M : ℝ) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (hw : ContinuousOn w (Icc (0 : ℝ) T))
    (h0 : ∀ t ∈ Icc (0 : ℝ) T,
      ‖torusSobolevInclusion 0 (torusSobolevInclusion 1 (v t)) -
        torusSobolevInclusion 0 (torusSobolevInclusion 1 (w t))‖ ≤ ε)
    (hv2 : (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤ M)
    (hw2 : (∫ t in (0 : ℝ)..T, ‖w t‖ ^ 2) ≤ M) :
    (∫ t in (0 : ℝ)..T,
      ‖torusSobolevInclusion 1 (v t) - torusSobolevInclusion 1 (w t)‖ ^ 2) ^ 2 ≤
        4 * ε ^ 2 * T * M := by
  have hdiff : ContinuousOn (fun t => v t - w t) (Icc (0 : ℝ) T) := hv.sub hw
  have h2 : (∫ t in (0 : ℝ)..T, ‖v t - w t‖ ^ 2) ≤ 4 * M := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..T, (2 * ‖v t‖ ^ 2 + 2 * ‖w t‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on hT
          ((hdiff.norm.pow 2).intervalIntegrable_of_Icc hT)
          (((continuousOn_const.mul (hv.norm.pow 2)).add
            (continuousOn_const.mul (hw.norm.pow 2))).intervalIntegrable_of_Icc hT)
        intro t ht
        change ‖v t - w t‖ ^ 2 ≤ 2 * ‖v t‖ ^ 2 + 2 * ‖w t‖ ^ 2
        have hn := pow_le_pow_left₀ (norm_nonneg (v t - w t))
          (norm_sub_le (v t) (w t)) 2
        nlinarith [sq_nonneg (‖v t‖ - ‖w t‖)]
      _ = 2 * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) +
          2 * (∫ t in (0 : ℝ)..T, ‖w t‖ ^ 2) := by
        have hvi : IntervalIntegrable (fun t : ℝ => 2 * ‖v t‖ ^ 2) volume 0 T :=
          ((hv.norm.pow 2).intervalIntegrable_of_Icc hT).const_mul 2
        have hwi : IntervalIntegrable (fun t : ℝ => 2 * ‖w t‖ ^ 2) volume 0 T :=
          ((hw.norm.pow 2).intervalIntegrable_of_Icc hT).const_mul 2
        calc
          _ = (∫ t in (0 : ℝ)..T, 2 * ‖v t‖ ^ 2) +
              ∫ t in (0 : ℝ)..T, 2 * ‖w t‖ ^ 2 :=
            intervalIntegral.integral_add hvi hwi
          _ = _ := by rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith
  have h := torusSobolev_H1_time_interpolation_of_energy_bound
    (fun t => v t - w t) T ε (4 * M) hT hε hdiff
    (fun t ht => by simpa only [map_sub] using h0 t ht) h2
  simpa only [map_sub, mul_assoc, mul_left_comm, mul_comm] using h

end

end SingularClosure
