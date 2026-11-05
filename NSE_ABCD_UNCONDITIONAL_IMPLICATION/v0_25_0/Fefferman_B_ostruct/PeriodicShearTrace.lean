import PeriodicShearGrowth
import PeriodicShearProfile
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace CondFeffB

open Set Filter
open scoped Topology

private def damping (a : ℝ) (k : ℕ) : ℝ := -(a * ((k + 1 : ℕ) : ℝ) ^ 2)

private def jetTerm (a : ℝ) (m k : ℕ) (t : ℝ) : ℝ :=
  (damping a k ^ m * Real.exp (-((k + 1 : ℕ) : ℝ))) * Real.exp (damping a k * t)

private def jetSum (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑' k : ℕ, jetTerm a m k t

private def majorant (a : ℝ) (m k : ℕ) : ℝ :=
  a ^ m * PeriodicShear.weightedPower (2 * m) (k + 1)

private theorem summable_majorant (a : ℝ) (m : ℕ) : Summable (majorant a m) := by
  exact (PeriodicShear.summable_weightedPower_succ (2 * m)).mul_left (a ^ m)

private theorem norm_jetTerm_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (m k : ℕ) :
    ‖jetTerm a m k t‖ ≤ majorant a m k := by
  have hd : damping a k ≤ 0 := neg_nonpos.mpr (mul_nonneg ha (sq_nonneg _))
  have he : Real.exp (damping a k * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg hd ht)
  have hdabs : |damping a k| = a * ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [damping, abs_neg, abs_of_nonneg (mul_nonneg ha (sq_nonneg _))]
  simp only [jetTerm, Real.norm_eq_abs, abs_mul, abs_pow, hdabs,
    Real.abs_exp]
  calc
    _ ≤ ((a * ((k + 1 : ℕ) : ℝ) ^ 2) ^ m * Real.exp (-((k + 1 : ℕ) : ℝ))) * 1 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by simp only [majorant, PeriodicShear.weightedPower,
      mul_one, mul_pow, ← pow_mul, mul_assoc]

private theorem hasDerivAt_jetTerm (a : ℝ) (m k : ℕ) (t : ℝ) :
    HasDerivAt (jetTerm a m k) (jetTerm a (m + 1) k t) t := by
  have he := (hasDerivAt_const_mul (x := t) (damping a k)).exp
  have h := he.const_mul (damping a k ^ m * Real.exp (-((k + 1 : ℕ) : ℝ)))
  change HasDerivAt
    (fun s : ℝ => (damping a k ^ m * Real.exp (-((k + 1 : ℕ) : ℝ))) *
      Real.exp (damping a k * s))
    ((damping a k ^ (m + 1) * Real.exp (-((k + 1 : ℕ) : ℝ))) *
      Real.exp (damping a k * t)) t
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

private theorem continuousOn_jetSum {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    ContinuousOn (jetSum a m) (Ici 0) := by
  exact continuousOn_tsum (f := jetTerm a m) (s := Ici (0 : ℝ))
    (fun k t _ => (hasDerivAt_jetTerm a m k t).continuousAt.continuousWithinAt)
    (summable_majorant a m) (fun k _ ht => norm_jetTerm_le ha ht m k)

private theorem hasDerivAt_jetSum {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (m : ℕ) :
    HasDerivAt (jetSum a m) (jetSum a (m + 1) t) t := by
  refine hasDerivAt_tsum_of_isPreconnected (g := jetTerm a m)
    (g' := jetTerm a (m + 1)) (t := Ioi (0 : ℝ)) (y₀ := 1)
    (summable_majorant a (m + 1)) isOpen_Ioi isPreconnected_Ioi
    (fun k s _ => hasDerivAt_jetTerm a m k s)
    (fun k s hs => norm_jetTerm_le ha (le_of_lt hs) (m + 1) k)
    (show (0 : ℝ) < 1 by norm_num) ?_ ht
  exact (summable_majorant a m).of_norm_bounded
    (fun k => norm_jetTerm_le ha (by norm_num : 0 ≤ (1 : ℝ)) m k)

private theorem hasDerivWithinAt_jetSum {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (m : ℕ) :
    HasDerivWithinAt (jetSum a m) (jetSum a (m + 1) t) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    have hcont (j : ℕ) : ContinuousWithinAt (jetSum a j) (Ioi 0) 0 :=
      (continuousOn_jetSum ha j 0 self_mem_Ici).mono Ioi_subset_Ici_self
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi (0 : ℝ))
      (fun y hy => (hasDerivAt_jetSum ha hy m).differentiableAt.differentiableWithinAt)
      (hcont m) self_mem_nhdsWithin
    apply (hcont (m + 1)).tendsto.congr'
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with x hx
    exact (hasDerivAt_jetSum ha hx m).deriv.symm
  · exact (hasDerivAt_jetSum ha h m).hasDerivWithinAt

private theorem iterated_jetSum {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    EqOn (iteratedDerivWithin m (jetSum a 0) (Ici 0)) (jetSum a m) (Ici 0) := by
  induction m with
  | zero => simp [iteratedDerivWithin_zero, EqOn]
  | succ m ih =>
    intro t ht
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih ht)]
    exact (hasDerivWithinAt_jetSum ha ht m).derivWithin (uniqueDiffOn_Ici 0 t ht)

private theorem jetSum_zero_eq (a : ℝ) (m : ℕ) :
    jetSum a m 0 =
      (-a) ^ m * ∑' k : ℕ, PeriodicShear.weightedPower (2 * m) (k + 1) := by
  rw [jetSum, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [jetTerm, damping, mul_zero, Real.exp_zero, mul_one,
    PeriodicShear.weightedPower, ← neg_mul, mul_pow, ← pow_mul, mul_assoc]

/-- Right derivatives at the initial time of the actual periodic Fourier shear. -/
theorem abs_shearTraceJet_eq_moment {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    |iteratedDerivWithin m (fun t => shearProfile ν t 0) (Ici 0) 0| =
      PeriodicShear.moment (4 * Real.pi ^ 2 * ν) m := by
  let a : ℝ := 4 * Real.pi ^ 2 * ν
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have htrace : (fun t => shearProfile ν t 0) = jetSum a 0 := by
    funext t
    unfold shearProfile jetSum
    apply tsum_congr
    intro k
    rw [shearMode_at_origin]
    simp only [jetTerm, damping, a, pow_zero, one_mul]
    <;> ring
  have hnonneg : 0 ≤ ∑' k : ℕ, PeriodicShear.weightedPower (2 * m) (k + 1) := by
    apply tsum_nonneg
    intro k
    unfold PeriodicShear.weightedPower
    positivity
  rw [htrace, iterated_jetSum ha m (show (0 : ℝ) ∈ Ici 0 from self_mem_Ici),
    jetSum_zero_eq, abs_mul, abs_pow, abs_neg, abs_of_nonneg ha, abs_of_nonneg hnonneg] <;> rfl

#print axioms abs_shearTraceJet_eq_moment

end CondFeffB
