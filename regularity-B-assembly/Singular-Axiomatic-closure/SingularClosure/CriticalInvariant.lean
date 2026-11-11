import SingularClosure.LinearBudget

/-!
# The critical small-data invariant and its sharp square budget

All hypotheses are scalar differential identities or inequalities on a finite
interval. The invariant is proved by a strict affine barrier. No invariant,
continuation certificate, or integral budget is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

/-- A local sign condition below a fixed upper barrier propagates the initial
upper bound. The derivative at zero is only a right derivative. -/
theorem scalar_invariant_of_deriv_nonpos_below
    {A d : ℝ → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T) (hab : a < b)
    (hA : ContinuousOn A (Icc 0 T)) (hinit : A 0 ≤ a)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hbound : ∀ t ∈ Ico 0 T, A t ≤ b → d t ≤ 0) :
    ∀ t ∈ Icc 0 T, A t ≤ a := by
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  let r : ℝ := min ε ((b - a) / 2)
  let η : ℝ := r / (T + 1)
  have hr : 0 < r := lt_min hε (by linarith)
  have hη : 0 < η := div_pos hr (by linarith)
  have hηmul : η * (T + 1) = r := by
    dsimp [η]
    exact div_mul_cancel₀ r (by linarith)
  have hbarrier : ∀ x ∈ Icc 0 T, a + η * x ≤ b := by
    intro x hx
    have hxmul := mul_le_mul_of_nonneg_left hx.2 hη.le
    have hrb : r ≤ (b - a) / 2 := min_le_right _ _
    nlinarith
  have hfence : ∀ x ∈ Icc 0 T, A x ≤ a + η * x := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f' := d) (B' := fun _ => η) hA
    · intro x hx
      exact (hderiv x hx).mono (fun y hy => hx.1.trans hy)
    · simpa only [mul_zero, add_zero] using hinit
    · intro x
      simpa only [mul_one] using
        ((hasDerivAt_id x).const_mul η).const_add a
    · intro x hx heq
      have hxbound : A x ≤ b := by
        rw [heq]
        exact hbarrier x ⟨hx.1, hx.2.le⟩
      exact (hbound x hx hxbound).trans_lt hη
  have hrε : r ≤ ε := min_le_left _ _
  have htmul := mul_le_mul_of_nonneg_left ht.2 hη.le
  have hfinal : a + η * t ≤ a + ε := by nlinarith
  exact (hfence t ht).trans hfinal

/-- The critical Galerkin bootstrap, with a norm upper bound `a₀` and the
squared critical energy `A`. The condition is the strict gap `C*a₀ < ν`. -/
theorem CRITICAL_ENERGY_INVARIANT
    {A B d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0) :
    ∀ t ∈ Icc 0 T, A t ≤ a₀ ^ 2 := by
  have hr : ∃ r : ℝ, a₀ < r ∧ C * r < ν := by
    by_cases hzero : C = 0
    · refine ⟨a₀ + 1, by linarith, ?_⟩
      simpa only [hzero, zero_mul] using hsmall
    · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
      have hquot : a₀ < ν / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
      obtain ⟨r, har, hrν⟩ := exists_between hquot
      refine ⟨r, har, ?_⟩
      have hrC := (lt_div_iff₀ hCpos).1 hrν
      nlinarith
  obtain ⟨r, har, hrν⟩ := hr
  have hrpos : 0 < r := lt_of_le_of_lt ha₀ har
  apply scalar_invariant_of_deriv_nonpos_below hT
    (show a₀ ^ 2 < r ^ 2 by nlinarith) hA hinit hderiv
  intro t ht hAt
  have hsqrt : Real.sqrt (A t) ≤ r := by
    calc
      Real.sqrt (A t) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hAt
      _ = r := Real.sqrt_sq hrpos.le
  have hgap : 0 ≤ ν - C * Real.sqrt (A t) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hC
    linarith
  have hprod := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgap) (hB t ht)
  linarith [hcritical t ht]

/-- Once the critical norm is invariant, the actual dissipation has the
uniform coefficient `2*(ν-C*a₀)`. -/
theorem critical_uniform_dissipation_inequality
    {A B d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0) :
    ∀ t ∈ Ico 0 T, d t + 2 * (ν - C * a₀) * B t ≤ 0 := by
  have hinvariant := CRITICAL_ENERGY_INVARIANT hT hC ha₀ hsmall hA hB hinit hderiv
    hcritical
  intro t ht
  have hsqrt : Real.sqrt (A t) ≤ a₀ := by
    calc
      Real.sqrt (A t) ≤ Real.sqrt (a₀ ^ 2) :=
        Real.sqrt_le_sqrt (hinvariant t ⟨ht.1, ht.2.le⟩)
      _ = a₀ := Real.sqrt_sq ha₀
  have hgap : ν - C * a₀ ≤ ν - C * Real.sqrt (A t) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hC
    linarith
  have hmul := mul_le_mul_of_nonneg_right hgap (hB t ht)
  linarith [hcritical t ht]

/-- The sharp square budget. Here `X` is the squared homogeneous H¹ norm,
so the integrand `X²` is exactly the fourth power of the physical gradient
L² norm. The coefficient is four, not two. -/
theorem CRITICAL_SQUARE_BUDGET
    {A B X d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hX : ContinuousOn X (Icc 0 T))
    (hAnonneg : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0)
    (hinterp : ∀ t ∈ Ioo 0 T, X t ^ 2 ≤ A t * B t) :
    ∀ t ∈ Icc 0 T,
      A t ^ 2 + 4 * (ν - C * a₀) * (∫ s in (0 : ℝ)..t, X s ^ 2) ≤ A 0 ^ 2 := by
  have hδ : 0 < ν - C * a₀ := sub_pos.mpr hsmall
  have hlinear := critical_uniform_dissipation_inequality hT hC ha₀ hsmall
    hA hB hinit hderiv hcritical
  have hd2 : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => A s ^ 2) (2 * A t * d t) t := by
    intro t ht
    have hd := ((hderiv t ⟨ht.1.le, ht.2⟩).hasDerivAt (Ici_mem_nhds ht.1)).fun_pow 2
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd
  have hineq : ∀ t ∈ Ioo 0 T,
      2 * A t * d t + (4 * (ν - C * a₀)) * X t ^ 2 ≤ (0 : ℝ) * A t ^ 2 := by
    intro t ht
    have hApos := hAnonneg t ⟨ht.1.le, ht.2.le⟩
    have hm := mul_le_mul_of_nonneg_left (hlinear t ⟨ht.1.le, ht.2⟩)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hApos)
    have hi := mul_le_mul_of_nonneg_left (hinterp t ht)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hδ.le)
    nlinarith only [hm, hi]
  have h := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET
    (y := fun t => A t ^ 2) (z := X) (d := fun t => 2 * A t * d t)
    (a := fun _ => (0 : ℝ)) (ν := 4 * (ν - C * a₀)) (M := 0) (y₀ := A 0 ^ 2)
    (mul_nonneg (by norm_num) hδ.le) hT (hA.pow 2) hX continuousOn_const
    (fun t _ => sq_nonneg (A t)) (fun _ _ => le_rfl) le_rfl hd2 hineq
    (by simp)
  simpa only [Real.exp_zero, mul_one] using h

/-- Explicit datumwise budget, retaining the terminal critical energy. -/
theorem CRITICAL_SQUARE_BUDGET_DIV
    {A B X d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hX : ContinuousOn X (Icc 0 T))
    (hAnonneg : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0)
    (hinterp : ∀ t ∈ Ioo 0 T, X t ^ 2 ≤ A t * B t) :
    (∫ s in (0 : ℝ)..T, X s ^ 2) ≤
      (a₀ ^ 4 - A T ^ 2) / (4 * (ν - C * a₀)) := by
  have h := CRITICAL_SQUARE_BUDGET hT hC ha₀ hsmall hA hX hAnonneg hB hinit
    hderiv hcritical hinterp T ⟨hT, le_rfl⟩
  have hA0 := hAnonneg 0 ⟨le_rfl, hT⟩
  have hsq : A 0 ^ 2 ≤ a₀ ^ 4 := by nlinarith [sq_nonneg (a₀ ^ 2 - A 0)]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (sub_pos.mpr hsmall))).2
  nlinarith

end SingularClosure
