import SingularClosure.CriticalTrace
import SingularClosure.CriticalSpaces

/-!
# Actual finite Fourier-band trace estimate

The H^(1/2) energy derivative is paired exactly between the H^(3/2)
coefficient vector and the H^(-1/2) derivative vector. Only coordinate
absolute continuity and its actual a.e. derivative enter the theorem.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Interval Topology ENNReal

namespace SingularClosure

noncomputable section

/-- Actual finite weighted coefficient vector over a prescribed band. -/
def criticalFiniteBandState (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff) :
    EuclideanSpace ℂ ↥s :=
  WithLp.toLp 2 (fun ki => criticalWeightedCoeff q c ki.val)

theorem criticalFiniteBandState_norm_sq (q : ℤ) (s : Finset FourierIndex)
    (c : FourierCoeff) :
    ‖criticalFiniteBandState q s c‖ ^ 2 =
      ∑ ki : ↥s, criticalFrequencyWeight ki.val.1 ^ q *
        Complex.normSq (c ki.val.1 ki.val.2) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ki _
  change ‖criticalWeightedCoeff q c ki.val‖ ^ 2 = _
  rw [criticalWeightedCoeff_norm, mul_pow, criticalHalfWeight_zpow_sq,
    Complex.normSq_eq_norm_sq]

/-- The critical energy pairing is exactly a dual pairing two orders apart. -/
theorem criticalFiniteBandState_dual_pairing (s : Finset FourierIndex)
    (c r : FourierCoeff) :
    inner ℂ (criticalFiniteBandState 1 s c) (criticalFiniteBandState 1 s r) =
      inner ℂ (criticalFiniteBandState 3 s c) (criticalFiniteBandState (-1) s r) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ki _
  change inner ℂ (criticalWeightedCoeff 1 c ki.val)
      (criticalWeightedCoeff 1 r ki.val) =
    inner ℂ (criticalWeightedCoeff 3 c ki.val)
      (criticalWeightedCoeff (-1) r ki.val)
  simp only [criticalWeightedCoeff, zpow_one, zpow_neg_one, zpow_ofNat]
  rw [RCLike.inner_apply, RCLike.inner_apply]
  have hw : (starRingEnd ℂ) (criticalHalfWeight ki.val.1 : ℂ) =
      (criticalHalfWeight ki.val.1 : ℂ) := Complex.conj_ofReal _
  simp only [map_mul, map_pow, hw]
  field_simp [criticalHalfWeight_complex_ne_zero ki.val.1]

theorem criticalFiniteBandState_dual_bound (s : Finset FourierIndex)
    (c r : FourierCoeff) :
    |(inner ℂ (criticalFiniteBandState 1 s c) (criticalFiniteBandState 1 s r)).re| ≤
      ‖criticalFiniteBandState (-1) s r‖ * ‖criticalFiniteBandState 3 s c‖ := by
  rw [criticalFiniteBandState_dual_pairing]
  calc
    _ ≤ ‖inner ℂ (criticalFiniteBandState 3 s c)
        (criticalFiniteBandState (-1) s r)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖criticalFiniteBandState 3 s c‖ *
        ‖criticalFiniteBandState (-1) s r‖ := norm_inner_le_norm _ _
    _ = _ := mul_comm _ _

theorem criticalFiniteBandState_hasDerivAt (q : ℤ) (s : Finset FourierIndex)
    (c r : ℝ → FourierCoeff) {t : ℝ}
    (hc : ∀ ki : ↥s, HasDerivAt (fun τ => c τ ki.val.1 ki.val.2)
      (r t ki.val.1 ki.val.2) t) :
    HasDerivAt (fun τ => criticalFiniteBandState q s (c τ))
      (criticalFiniteBandState q s (r t)) t := by
  have hv : HasDerivAt
      (fun τ (ki : ↥s) => criticalWeightedCoeff q (c τ) ki.val)
      (fun ki : ↥s => criticalWeightedCoeff q (r t) ki.val) t := by
    apply hasDerivAt_pi.mpr
    intro ki
    exact (hc ki).const_mul ((criticalHalfWeight ki.val.1 : ℂ) ^ q)
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
    (fun ki : ↥s => criticalWeightedCoeff q (c t) ki.val)).comp_hasDerivAt t hv
  exact h

theorem criticalFiniteBandEnergy_hasDerivAt (s : Finset FourierIndex)
    (c r : ℝ → FourierCoeff) {t : ℝ}
    (hc : ∀ ki : ↥s, HasDerivAt (fun τ => c τ ki.val.1 ki.val.2)
      (r t ki.val.1 ki.val.2) t) :
    HasDerivAt (fun τ => ‖criticalFiniteBandState 1 s (c τ)‖ ^ 2)
      (2 * (inner ℂ (criticalFiniteBandState 1 s (c t))
        (criticalFiniteBandState 1 s (r t))).re) t := by
  have hinner : inner ℝ (criticalFiniteBandState 1 s (c t))
      (criticalFiniteBandState 1 s (r t)) =
      (inner ℂ (criticalFiniteBandState 1 s (c t))
        (criticalFiniteBandState 1 s (r t))).re := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ki _
    exact real_inner_eq_re_inner ℂ _ _
  simpa only [hinner] using (criticalFiniteBandState_hasDerivAt 1 s c r hc).norm_sq

private theorem criticalTrace_ac_finset_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      simp only [Finset.sum_empty, AbsolutelyContinuousOnInterval, dist_self,
        Finset.sum_const_zero]
      exact tendsto_const_nhds
  | @insert i s hi ih =>
      intro hf
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).fun_add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Coordinate AC proves finite-band energy AC; it is not an admission. -/
theorem criticalFiniteBandEnergy_absolutelyContinuous
    (s : Finset FourierIndex) (c : ℝ → FourierCoeff) {T : ℝ}
    (hre : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).re) 0 T)
    (him : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).im) 0 T) :
    AbsolutelyContinuousOnInterval
      (fun t => ‖criticalFiniteBandState 1 s (c t)‖ ^ 2) 0 T := by
  simp_rw [criticalFiniteBandState_norm_sq, zpow_one]
  apply criticalTrace_ac_finset_sum
  intro ki _
  apply AbsolutelyContinuousOnInterval.const_mul
  simpa only [Complex.normSq_apply] using
    ((hre ki).fun_mul (hre ki)).fun_add ((him ki).fun_mul (him ki))

/-- The exact stage-7 estimate for every actual finite Fourier band. -/
theorem CRITICAL_FINITE_FOURIER_BAND_TRACE_BOUND
    (s : Finset FourierIndex) (c r : ℝ → FourierCoeff) {T : ℝ} (hT : 0 < T)
    (hre : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).re) 0 T)
    (him : ∀ ki : ↥s,
      AbsolutelyContinuousOnInterval (fun t => (c t ki.val.1 ki.val.2).im) 0 T)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ki : ↥s,
      HasDerivAt (fun τ => c τ ki.val.1 ki.val.2) (r t ki.val.1 ki.val.2) t)
    (hlo : MemLp (fun t => ‖criticalFiniteBandState (-1) s (r t)‖) 2
      (volume.restrict (Icc (0 : ℝ) T)))
    (hhi : MemLp (fun t => ‖criticalFiniteBandState 3 s (c t)‖) 2
      (volume.restrict (Icc (0 : ℝ) T))) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖criticalFiniteBandState 1 s (c t)‖ ^ 2 ≤
        (∫ τ in (0 : ℝ)..T, ‖criticalFiniteBandState 1 s (c τ)‖ ^ 2) / T +
          2 * Real.sqrt (∫ τ in (0 : ℝ)..T,
            ‖criticalFiniteBandState (-1) s (r τ)‖ ^ 2) *
            Real.sqrt (∫ τ in (0 : ℝ)..T,
              ‖criticalFiniteBandState 3 s (c τ)‖ ^ 2) := by
  apply CRITICAL_BAND_ENERGY_TRACE_BOUND
    (fun t => ‖criticalFiniteBandState 1 s (c t)‖ ^ 2)
    (fun t => ‖criticalFiniteBandState (-1) s (r t)‖)
    (fun t => ‖criticalFiniteBandState 3 s (c t)‖) hT
    (criticalFiniteBandEnergy_absolutelyContinuous s c hre him) hlo hhi
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (Filter.Eventually.of_forall (fun t => norm_nonneg _))
  filter_upwards [hderiv] with t ht
  rw [(criticalFiniteBandEnergy_hasDerivAt s c r ht).deriv, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (criticalFiniteBandState_dual_bound s (c t) (r t))
    (by norm_num)

end

end SingularClosure
