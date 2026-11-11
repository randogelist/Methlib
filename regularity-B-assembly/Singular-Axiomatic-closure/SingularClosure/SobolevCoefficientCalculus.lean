import SingularClosure.SobolevLimitBounds
import SingularClosure.SobolevTrajectoryCalculus

/-!
# Continuity and differentiation from the actual Fourier coefficients

A uniform bound one Sobolev order higher upgrades coefficientwise continuity
to strong continuity. Continuous linear coefficient evaluation commutes with
the Bochner integral, so scalar coefficient integral equations identify the
actual Hilbert-valued integral and derivative, including the initial time.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal

namespace SingularClosure

noncomputable section

theorem torusSobolev_memLp_Icc_of_continuousOn
    (s : ℕ) (u : ℝ → TorusSobolev s) (T : ℝ) (p : ℝ≥0∞)
    (hu : ContinuousOn u (Icc (0 : ℝ) T)) :
    MemLp u p (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) := ⟨by simp⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  apply MemLp.of_bound
    (hu.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

theorem torusSobolevInclusion_continuousOn_of_coeff_continuousOn
    {α : Type*} [TopologicalSpace α] (s : ℕ) (u : α → TorusSobolev (s + 1))
    (S : Set α) (B : ℝ) (hbound : ∀ x ∈ S, ‖u x‖ ≤ B)
    (hcoeff : ∀ k i, ContinuousOn (fun x => (u x).val k i) S) :
    ContinuousOn (fun x => torusSobolevInclusion s (u x)) S := by
  intro x hx
  apply torusSobolevInclusion_tendsto_of_coeff_tendsto s u
    (torusSobolevInclusion s (u x)) B
  · exact Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hbound y hy)
  · intro k i
    exact hcoeff k i x hx

theorem torusSobolevCoeff_intervalIntegral
    (s : ℕ) (r : ℝ → TorusSobolev s) (a b : ℝ)
    (hr : IntervalIntegrable r volume a b) (k : Frequency) (i : Fin 3) :
    (∫ t in a..b, r t).val k i = ∫ t in a..b, (r t).val k i := by
  simpa only [torusSobolevCoeff_apply] using!
    ((torusSobolevCoeff s k i).intervalIntegral_comp_comm hr).symm

/-- Scalar Fourier integral identities determine the actual Bochner integral. -/
theorem torusSobolev_integral_eq_of_coefficient_integral
    (s : ℕ) (u r : ℝ → TorusSobolev s) (t : ℝ)
    (hr : IntervalIntegrable r volume 0 t)
    (hcoeff : ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i + ∫ z in (0 : ℝ)..t, (r z).val k i) :
    u t = u 0 + ∫ z in (0 : ℝ)..t, r z := by
  apply Subtype.ext
  funext k i
  change (u t).val k i = (u 0).val k i + (∫ z in (0 : ℝ)..t, r z).val k i
  rw [torusSobolevCoeff_intervalIntegral s r 0 t hr k i]
  exact hcoeff k i

/-- The actual Hilbert-valued derivative follows from continuous RHS coefficients
and their integral equation. The derivative at zero is taken within Ici 0. -/
theorem torusSobolev_hasDerivWithinAt_of_coefficient_integral
    (s : ℕ) (u r : ℝ → TorusSobolev s) (hr : ContinuousOn r (Ici 0))
    (hcoeff : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i + ∫ z in (0 : ℝ)..t, (r z).val k i)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt u (r t) (Ici 0) t := by
  let r' : ℝ → TorusSobolev s := fun z => r (max z 0)
  have hr' : Continuous r' := by
    exact hr.comp_continuous (continuous_id.max continuous_const)
      (fun z => le_max_right z 0)
  have hidentity (z : ℝ) (hz : 0 ≤ z) :
      u z = u 0 + ∫ y in (0 : ℝ)..z, r' y := by
    have hri : IntervalIntegrable r volume 0 z :=
      (hr.mono (fun y hy => hy.1)).intervalIntegrable_of_Icc hz
    rw [torusSobolev_integral_eq_of_coefficient_integral s u r z hri (hcoeff z hz)]
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    have hm : y ∈ Icc (0 : ℝ) z := by simpa only [uIcc_of_le hz] using hy
    simp only [r', max_eq_left hm.1]
  have hd : HasDerivWithinAt
      (fun z => u 0 + ∫ y in (0 : ℝ)..z, r' y) (r' t) (Ici 0) t :=
    ((hr'.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (u 0)).hasDerivWithinAt
  have hu := hd.congr_of_mem (fun z hz => hidentity z hz) ht
  simpa only [r', max_eq_left ht] using hu

end

end SingularClosure
