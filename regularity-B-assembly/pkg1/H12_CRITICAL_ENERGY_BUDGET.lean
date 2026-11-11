import H12_CRITICAL_ABSORPTION
import Mathlib

/-!
# Critical energy and the square-enstrophy budget

All statements in this module are scalar analytic implications.  In the
intended finite Galerkin application, `H = ‖u_N‖_{H^(1/2)}²`,
`D = ‖u_N‖_{H^(3/2)}²`, and `E = ‖∇u_N‖₂²`.  This module neither
defines an NSE solution nor assumes that these identifications have been
implemented.  The interpolation and energy-law hypotheses are explicit.

The final scalar bootstrap starts only from the differential inequality
and initial critical smallness: it does not assume the desired budget or
the persistence of smallness.  External compilation and exact theorem
axiom audits are required before promotion from candidate status.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace H12CriticalEnergyBudget

/-- The positive coefficient in the absorbed critical energy law. -/
def dissipationCoefficient (ν θ : ℝ) : ℝ := 2 * (1 - θ) * ν

theorem dissipationCoefficient_pos {ν θ : ℝ}
    (hν : 0 < ν) (hθ : θ < 1) :
    0 < dissipationCoefficient ν θ := by
  unfold dissipationCoefficient
  have : 0 < 1 - θ := sub_pos.mpr hθ
  positivity

/-- An integrated critical energy law and spectral interpolation imply
the square-enstrophy estimate.  No square-enstrophy budget is assumed. -/
theorem H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY
    {H D E : ℝ → ℝ} {ν θ T H₀ : ℝ}
    (hν : 0 < ν) (hθ : θ < 1) (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (henergy : ∀ t ∈ Icc 0 T,
      H t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D s) ≤ H₀)
    (hinterpolation : ∀ t ∈ Icc 0 T, (E t) ^ 2 ≤ H t * D t) :
    (∀ t ∈ Icc 0 T, H t ≤ H₀) ∧
      (∫ s in (0 : ℝ)..T, D s) ≤ H₀ / dissipationCoefficient ν θ ∧
      (∫ s in (0 : ℝ)..T, (E s) ^ 2) ≤
        H₀ ^ 2 / dissipationCoefficient ν θ := by
  have hk : 0 < dissipationCoefficient ν θ := dissipationCoefficient_pos hν hθ
  have hH_bound : ∀ t ∈ Icc 0 T, H t ≤ H₀ := by
    intro t ht
    have hi : 0 ≤ ∫ s in (0 : ℝ)..t, D s := by
      apply intervalIntegral.integral_nonneg ht.1
      intro s hs
      exact hD_nonneg s ⟨hs.1, hs.2.trans ht.2⟩
    have hki := mul_nonneg hk.le hi
    linarith [henergy t ht]
  have hD_bound : (∫ s in (0 : ℝ)..T, D s) ≤
      H₀ / dissipationCoefficient ν θ := by
    apply (le_div_iff₀ hk).2
    have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have hn := hH_nonneg T hTmem
    have he := henergy T hTmem
    nlinarith
  have hEi : IntervalIntegrable (fun s => (E s) ^ 2) volume 0 T :=
    (hE.pow 2).intervalIntegrable_of_Icc hT
  have hDi : IntervalIntegrable (fun s => H₀ * D s) volume 0 T :=
    (continuousOn_const.mul hD).intervalIntegrable_of_Icc hT
  have hpoint : ∀ t ∈ Icc 0 T, (E t) ^ 2 ≤ H₀ * D t := by
    intro t ht
    exact (hinterpolation t ht).trans
      (mul_le_mul_of_nonneg_right (hH_bound t ht) (hD_nonneg t ht))
  have hE_bound : (∫ s in (0 : ℝ)..T, (E s) ^ 2) ≤
      H₀ ^ 2 / dissipationCoefficient ν θ := by
    calc
      (∫ s in (0 : ℝ)..T, (E s) ^ 2)
          ≤ ∫ s in (0 : ℝ)..T, H₀ * D s :=
        intervalIntegral.integral_mono_on hT hEi hDi hpoint
      _ = H₀ * (∫ s in (0 : ℝ)..T, D s) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ H₀ * (H₀ / dissipationCoefficient ν θ) :=
        mul_le_mul_of_nonneg_left hD_bound hH₀
      _ = H₀ ^ 2 / dissipationCoefficient ν θ := by ring
  exact ⟨hH_bound, hD_bound, hE_bound⟩

/-- Uniformity in the Galerkin index follows from a common critical
initial bound and common viscosity/smallness margin. -/
theorem H12_UNIFORM_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY
    {ι : Type*} {H D E : ι → ℝ → ℝ} {ν θ T H₀ : ℝ}
    (hν : 0 < ν) (hθ : θ < 1) (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (henergy : ∀ n t, t ∈ Icc 0 T →
      H n t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D n s) ≤ H₀)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t) :
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      H₀ ^ 2 / (2 * (1 - θ) * ν) := by
  intro n
  simpa only [dissipationCoefficient] using
    (H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY hν hθ hT hH₀
      (hD n) (hE n) (hH_nonneg n) (hD_nonneg n)
      (henergy n) (hinterpolation n)).2.2

private theorem primitive_continuousOn_Icc
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
  have hi : IntervalIntegrable f volume 0 T := hf.intervalIntegrable_of_Icc hT
  simpa only [uIcc_of_le hT] using
    (intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T))

private theorem primitive_hasDerivAt_Ioo
    {f : ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, f s) (f t) t := by
  have hi : IntervalIntegrable f volume 0 t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter f (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- The accumulated dissipation is obtained from a differential law by
the fundamental theorem of calculus and derivative monotonicity. -/
theorem critical_energy_of_absorbed_differential
    {H D d : ℝ → ℝ} {k T H₀ : ℝ}
    (hT : 0 ≤ T)
    (hH : ContinuousOn H (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀)
    (habsorbed : ∀ t ∈ Ioo 0 T, d t + k * D t ≤ 0) :
    ∀ t ∈ Icc 0 T, H t + k * (∫ s in (0 : ℝ)..t, D s) ≤ H₀ := by
  let Q : ℝ → ℝ := fun t => H t + k * (∫ s in (0 : ℝ)..t, D s)
  have hQc : ContinuousOn Q (Icc 0 T) :=
    hH.add (continuousOn_const.mul (primitive_continuousOn_Icc hT hD))
  have hQd : ∀ t ∈ Ioo 0 T, HasDerivAt Q (d t + k * D t) t := by
    intro t ht
    exact (hderiv t ht).add ((primitive_hasDerivAt_Ioo hD ht).const_mul k)
  have hanti : AntitoneOn Q (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T) hQc
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      exact (hQd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      rw [(hQd t ht').deriv]
      exact habsorbed t ht'
  intro t ht
  have h := hanti ⟨le_rfl, hT⟩ ht ht.1
  have h' : H t + k * (∫ s in (0 : ℝ)..t, D s) ≤ H 0 := by
    simpa only [Q, intervalIntegral.integral_same, mul_zero, add_zero] using h
  exact h'.trans h_initial

/-- Scalar bootstrap: a continuous differentiable trajectory initially
strictly below a barrier cannot increase if its derivative is nonpositive
throughout the lower region.  Persistence below the barrier is proved,
not assumed. -/
theorem energy_bound_of_deriv_nonpos_below_barrier
    {H d : ℝ → ℝ} {T H₀ R : ℝ}
    (hT : 0 ≤ T) (hH : ContinuousOn H (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀) (hgap : H₀ < R)
    (hbelow : ∀ t ∈ Ico 0 T, H t ≤ R → d t ≤ 0) :
    ∀ t ∈ Icc 0 T, H t ≤ H₀ := by
  intro t ht
  by_contra hnot
  have hlt : H₀ < H t := lt_of_not_ge hnot
  let m : ℝ := min (H t - H₀) (R - H₀)
  let ε : ℝ := m / (2 * (T + 1))
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min (sub_pos.mpr hlt) (sub_pos.mpr hgap)
  have hTp : 0 < T + 1 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos hm (by positivity)
  have hεid : ε * (T + 1) = m / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hTp] <;> ring
  have hm₁ : m ≤ H t - H₀ := min_le_left _ _
  have hm₂ : m ≤ R - H₀ := min_le_right _ _
  have hεR : ε * (T + 1) < R - H₀ := by
    rw [hεid]
    linarith
  have hεt : ε * (T + 1) < H t - H₀ := by
    rw [hεid]
    linarith
  have hbound : ∀ ⦃s⦄, s ∈ Icc (0 : ℝ) T → H s ≤ H₀ + ε * (s + 1) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (B := fun s => H₀ + ε * (s + 1)) (B' := fun _ => ε)
      hH (fun s hs => (hderiv s hs).hasDerivWithinAt)
    · simp only [zero_add]
      linarith
    · intro s
      simpa using (hasDerivAt_const s H₀).add
        (((hasDerivAt_id s).add_const 1).const_mul ε)
    · intro s hs heq
      have hmul : ε * (s + 1) ≤ ε * (T + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) hε.le
      have hHs : H s ≤ R := by linarith
      exact (hbelow s hs hHs).trans_lt hε
  have hmul : ε * (t + 1) ≤ ε * (T + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) hε.le
  have hb := hbound ht
  linarith

/-- Actual scalar small-data bootstrap for the critical differential
inequality.  `H₀` is a squared norm, and smallness concerns `sqrt H₀`.
The derivative at time zero is required, as is available for a finite
Galerkin ODE.  No derivative at the terminal endpoint is required. -/
theorem H12_CRITICAL_ENERGY_OF_SMALL_DATA
    {H D d : ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ContinuousOn H (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * ν * D t ≤ 2 * C * Real.sqrt (H t) * D t) :
    ∀ t ∈ Icc 0 T,
      H t + dissipationCoefficient ν θ * (∫ s in (0 : ℝ)..t, D s) ≤ H₀ := by
  let r : ℝ := ν / C
  have hr : 0 < r := div_pos hν hC
  have hCr : C * r = ν := by
    dsimp [r]
    field_simp [ne_of_gt hC] <;> ring
  have hsqrt_lt : Real.sqrt H₀ < r := by
    have hθν : θ * ν < ν := by
      simpa only [one_mul] using (mul_lt_mul_of_pos_right hθ hν)
    have hstrict : C * Real.sqrt H₀ < ν := hsmall.trans_lt hθν
    dsimp [r]
    apply (lt_div_iff₀ hC).2
    simpa only [mul_comm] using hstrict
  have hgap : H₀ < r ^ 2 := by
    have hs := Real.sq_sqrt hH₀
    have hn := Real.sqrt_nonneg H₀
    nlinarith
  have hH_bound : ∀ t ∈ Icc 0 T, H t ≤ H₀ := by
    apply energy_bound_of_deriv_nonpos_below_barrier hT hH hderiv h_initial hgap
    intro t ht hbarrier
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hDt := hD_nonneg t ht'
    have hs := Real.sq_sqrt (hH_nonneg t ht')
    have hn := Real.sqrt_nonneg (H t)
    have hsqrt_le : Real.sqrt (H t) ≤ r := by nlinarith
    have hcoef : C * Real.sqrt (H t) ≤ ν := by
      calc
        C * Real.sqrt (H t) ≤ C * r :=
          mul_le_mul_of_nonneg_left hsqrt_le hC.le
        _ = ν := hCr
    have hmul := mul_le_mul_of_nonneg_right hcoef hDt
    nlinarith [hcritical t ht]
  apply critical_energy_of_absorbed_differential hT hH hD
    (fun t ht => hderiv t ⟨ht.1.le, ht.2⟩) h_initial
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hcoef : C * Real.sqrt (H t) ≤ θ * ν :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hH_bound t ht')) hC.le).trans hsmall
  have hmul := mul_le_mul_of_nonneg_right hcoef (hD_nonneg t ht')
  have he := hcritical t ⟨ht.1.le, ht.2⟩
  unfold dissipationCoefficient
  nlinarith

/-- Complete scalar implication from initial critical smallness and a
critical differential law to the explicit square-enstrophy budget. -/
theorem H12_SQUARE_ENSTROPHY_OF_SMALL_DATA
    {H D E d : ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ContinuousOn H (Icc 0 T))
    (hD : ContinuousOn D (Icc 0 T))
    (hE : ContinuousOn E (Icc 0 T))
    (hH_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ H t)
    (hD_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivAt H (d t) t)
    (h_initial : H 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * ν * D t ≤ 2 * C * Real.sqrt (H t) * D t)
    (hinterpolation : ∀ t ∈ Icc 0 T, (E t) ^ 2 ≤ H t * D t) :
    (∫ s in (0 : ℝ)..T, (E s) ^ 2) ≤ H₀ ^ 2 / (2 * (1 - θ) * ν) := by
  have henergy := H12_CRITICAL_ENERGY_OF_SMALL_DATA hν hC hθ hT hH₀
    hH hD hH_nonneg hD_nonneg hderiv h_initial hsmall hcritical
  simpa only [dissipationCoefficient] using
    (H12_SQUARE_ENSTROPHY_OF_CRITICAL_ENERGY hν hθ hT hH₀
      hD hE hH_nonneg hD_nonneg henergy hinterpolation).2.2

/-- The scalar small-data argument is uniform over any index type, in
particular the Galerkin cutoff.  The common initial bound is the only
quantity entering the final right-hand side. -/
theorem H12_UNIFORM_SQUARE_ENSTROPHY_OF_SMALL_DATA
    {ι : Type*} {H D E d : ι → ℝ → ℝ} {ν C θ T H₀ : ℝ}
    (hν : 0 < ν) (hC : 0 < C) (hθ : θ < 1)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (hH : ∀ n, ContinuousOn (H n) (Icc 0 T))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hE : ∀ n, ContinuousOn (E n) (Icc 0 T))
    (hH_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ H n t)
    (hD_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ D n t)
    (hderiv : ∀ n t, t ∈ Ico 0 T → HasDerivAt (H n) (d n t) t)
    (h_initial : ∀ n, H n 0 ≤ H₀)
    (hsmall : C * Real.sqrt H₀ ≤ θ * ν)
    (hcritical : ∀ n t, t ∈ Ico 0 T →
      d n t + 2 * ν * D n t ≤ 2 * C * Real.sqrt (H n t) * D n t)
    (hinterpolation : ∀ n t, t ∈ Icc 0 T → (E n t) ^ 2 ≤ H n t * D n t) :
    ∀ n, (∫ s in (0 : ℝ)..T, (E n s) ^ 2) ≤
      H₀ ^ 2 / (2 * (1 - θ) * ν) := by
  intro n
  exact H12_SQUARE_ENSTROPHY_OF_SMALL_DATA hν hC hθ hT hH₀
    (hH n) (hD n) (hE n) (hH_nonneg n) (hD_nonneg n)
    (hderiv n) (h_initial n) hsmall (hcritical n) (hinterpolation n)

end H12CriticalEnergyBudget
