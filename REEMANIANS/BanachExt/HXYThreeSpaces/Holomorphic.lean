import HXYThreeSpaces.HolomorphicForward
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convex.PathConnected

/-!
# Frozen candidate C3: reverse implication and exact RH equivalence

The reverse direction uses analytic continuation of a denominator-free defect
and finite analytic order. No positivity of the extension is assumed.
HolExt is not defined using RH or H00.

Prepared for external Lean 4.33.0 compilation. No local Lean execution.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory ComplexConjugate
open scoped Topology

namespace HXYThreeSpaces

open RH_HilbertLimit RH_HilbertLimit.TwoRoutes

theorem starConvex_Omega : StarConvex ℝ (0 : ℂ) Omega := by
  intro z hz a b ha hb hab
  change -1 < (a • (0 : ℂ) + b • z).re ∨
    (a • (0 : ℂ) + b • z).im ≠ 0
  simp only [smul_zero, zero_add, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  by_cases hbzero : b = 0
  · left
    simp [hbzero]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    have hbone : b ≤ 1 := by linarith
    rcases hz with hre | him
    · left
      have hprod : 0 < b * (z.re + 1) := mul_pos hbpos (by linarith)
      nlinarith
    · right
      exact mul_ne_zero hbzero him

theorem isPreconnected_Omega : IsPreconnected Omega :=
  (starConvex_Omega.isPathConnected zero_mem_Omega).isConnected.isPreconnected

/-- Germ matching propagates only after clearing the unknown denominator. -/
theorem holODE_of_holExt (h : HolExt) : HolODE := by
  rcases h with ⟨G, hG, hgerm⟩
  have hlocal : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      deriv normalizedXi z = G z * normalizedXi z := by
    filter_upwards [hgerm, eventually_normalizedXi_ne_zero] with z heq hne
    rw [normalizedLogDerivative_eq_logDerivative] at heq
    exact (div_eq_iff hne).mp heq
  let defect : ℂ → ℂ := fun z => deriv normalizedXi z - G z * normalizedXi z
  have hdefect : AnalyticOnNhd ℂ defect Omega := by
    intro z hz
    have hF := normalizedXi_entire z (Set.mem_univ z)
    exact hF.deriv.sub ((hG z hz).mul hF)
  have hdefectGerm : defect =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [hlocal] with z hz
    exact sub_eq_zero.mpr hz
  have hzeroOn : Set.EqOn defect 0 Omega :=
    hdefect.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_Omega zero_mem_Omega hdefectGerm
  refine ⟨G, hG, ?_⟩
  intro z hz
  exact sub_eq_zero.mp (hzeroOn hz)

theorem holExt_of_holODE (h : HolODE) : HolExt := by
  rcases h with ⟨G, hG, hode⟩
  refine ⟨G, hG, ?_⟩
  filter_upwards [isOpen_Omega.mem_nhds zero_mem_Omega,
    eventually_normalizedXi_ne_zero] with z hz hne
  rw [normalizedLogDerivative_eq_logDerivative]
  exact (div_eq_iff hne).mpr (hode z hz)

theorem holExt_iff_holODE : HolExt ↔ HolODE :=
  ⟨holODE_of_holExt, holExt_of_holODE⟩

/-- A globally nontrivial entire function cannot satisfy a holomorphic scalar
ODE near one of its zeros. The contradiction is between orders m and m-1. -/
theorem entire_local_ode_nonvanishing
    {Y A : ℂ → ℂ}
    (hY : AnalyticOnNhd ℂ Y Set.univ) (hYzero : Y 0 ≠ 0)
    {z : ℂ} (hA : AnalyticAt ℂ A z)
    (hode : ∀ᶠ w in 𝓝 z, deriv Y w = A w * Y w) : Y z ≠ 0 := by
  intro hzero
  have horderZero : analyticOrderAt Y 0 = 0 :=
    (hY 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hYzero
  have hfiniteZero : analyticOrderAt Y 0 ≠ ⊤ := by simp [horderZero]
  have hfinite : analyticOrderAt Y z ≠ ⊤ :=
    hY.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) hfiniteZero
  have hderiv : analyticOrderAt (deriv Y) z + 1 = analyticOrderAt Y z := by
    simpa [hzero] using (hY z (Set.mem_univ _)).analyticOrderAt_deriv_add_one
  have hmul : analyticOrderAt (deriv Y) z =
      analyticOrderAt A z + analyticOrderAt Y z := by
    calc
      _ = analyticOrderAt (fun w => A w * Y w) z := analyticOrderAt_congr hode
      _ = _ := analyticOrderAt_mul hA (hY z (Set.mem_univ _))
  have hle : analyticOrderAt Y z ≤ analyticOrderAt (deriv Y) z := by
    rw [hmul]
    simpa using add_le_add_right
      (show (0 : ℕ∞) ≤ analyticOrderAt A z from bot_le) (analyticOrderAt Y z)
  have hbad : analyticOrderAt Y z + 1 ≤ analyticOrderAt Y z := by
    calc
      analyticOrderAt Y z + 1 ≤ analyticOrderAt (deriv Y) z + 1 := by
        simpa only [add_comm] using (add_le_add_right hle (1 : ℕ∞))
      _ = analyticOrderAt Y z := hderiv
  generalize hq : analyticOrderAt Y z = q at hbad hfinite
  lift q to ℕ using hfinite with n hn
  norm_cast at hbad
  omega

theorem normalizedXi_nonzero_on_Omega_of_holODE (h : HolODE) :
    ∀ z ∈ Omega, normalizedXi z ≠ 0 := by
  rcases h with ⟨G, hG, hode⟩
  intro z hz
  apply entire_local_ode_nonvanishing normalizedXi_entire
    normalizedXi_zero_ne_zero (hG z hz)
  filter_upwards [isOpen_Omega.mem_nhds hz] with w hw
  exact hode w hw

theorem actual_theta_no_upper_zeros_of_holExt (h : HolExt) :
    ∀ z : ℂ, 0 < z.im → AWPIRH.theta z ≠ 0 := by
  have hnonzero := normalizedXi_nonzero_on_Omega_of_holODE (holODE_of_holExt h)
  intro z hz hzero
  have himpos : 0 < ((actualKappa : ℂ) * z).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos actualKappa_pos hz
  have hmem : (actualKappa : ℂ) * z ∈ Omega := Or.inr (ne_of_gt himpos)
  have harg : ((actualKappa : ℂ) * z) / (actualKappa : ℂ) = z := by
    exact (div_eq_iff actualKappa_complex_ne_zero).mpr (mul_comm _ _)
  apply hnonzero _ hmem
  simp only [normalizedXi, harg, hzero, zero_div]

theorem actual_theta_zero_real_of_holExt (h : HolExt)
    {z : ℂ} (hzero : AWPIRH.theta z = 0) : z.im = 0 := by
  have hUpper := actual_theta_no_upper_zeros_of_holExt h
  by_contra him
  by_cases hz : 0 < z.im
  · exact hUpper z hz hzero
  · have hneg : z.im < 0 := by
      by_contra hn
      exact him (le_antisymm (le_of_not_gt hz) (le_of_not_gt hn))
    have hconj : 0 < (conj z).im := by
      simpa only [Complex.conj_im] using neg_pos.mpr hneg
    exact hUpper (conj z) hconj (AngularMaster.theta_zero_conj hzero)

/-- C3 reverse endpoint. No positivity or spectral assumption is added to HolExt. -/
theorem nativeRH_of_holExt (h : HolExt) : _root_.RiemannHypothesis := by
  apply nativeRH_iff_xiZerosCritical.mpr
  intro s hs
  have hheight := AngularMaster.actual_xi_zero_one_lt_abs_im hs
  have him : s.im ≠ 0 := by
    intro himzero
    rw [himzero, abs_zero] at hheight
    norm_num at hheight
  have htheta : AWPIRH.theta ((s - (1 / 2 : ℂ)) ^ 2) = 0 := by
    rw [AWPIRH.theta_square]
    change AWPIRH.xi ((1 / 2 : ℂ) + (s - (1 / 2 : ℂ))) = 0
    have heq : (1 / 2 : ℂ) + (s - (1 / 2 : ℂ)) = s := by ring
    rw [heq]
    exact hs
  have hreal := actual_theta_zero_real_of_holExt h htheta
  have himsquare : ((s - (1 / 2 : ℂ)) ^ 2).im =
      2 * (s.re - (1 / 2 : ℝ)) * s.im := by
    simp [pow_two, Complex.mul_im]
    <;> ring
  rw [himsquare] at hreal
  have hmul : (s.re - (1 / 2 : ℝ)) * s.im = 0 := by nlinarith [hreal]
  have hre : s.re - (1 / 2 : ℝ) = 0 := (mul_eq_zero.mp hmul).resolve_right him
  linarith

theorem nativeRH_iff_holExt : _root_.RiemannHypothesis ↔ HolExt :=
  ⟨holExt_of_nativeRH, nativeRH_of_holExt⟩

theorem H00_iff_holExt : H00 ↔ HolExt :=
  H00_iff_nativeRH_route_one.trans nativeRH_iff_holExt

end HXYThreeSpaces
