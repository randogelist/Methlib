import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-!
The additive finite part is calibrated by the harmonic unit cells, extended
from the punctured plane by the residue-one criterion, and then used in the
multiplicative regularizer. The calibration and punctured little-o argument
adapt Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0, copyright 2024 David Loeffler,
authors David Loeffler and Terence Tao, under Apache 2.0.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace HVRNativeZetaPoleEquality

/-- On the real half-line, pole subtraction turns the Dirichlet sum into
the continuous expression formed from the sum of the unit-interval cells. -/
theorem real_dirichlet_finite_part_eq_cells {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1) =
      1 - s * ZetaAsymptotics.termTSum s := by
  rw [ZetaAsymptotics.termTSum_of_lt hs]
  generalize (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) = D
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs).ne'
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  field_simp [hs0, hs1] <;> ring

/-- At one the summed cells have value `1 − γ`. Their right continuity
therefore calibrates the finite part of the actual zeta function to `γ`. -/
theorem zeta_finite_part_tendsto_real_right :
    Tendsto (fun s : ℝ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[>] 1)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hat : ZetaAsymptotics.termTSum 1 = 1 - Real.eulerMascheroniConstant :=
    ZetaAsymptotics.term_tsum_one.tsum_eq
  have hcells : Tendsto ZetaAsymptotics.termTSum (𝓝[>] 1)
      (𝓝 (ZetaAsymptotics.termTSum 1)) :=
    (ZetaAsymptotics.continuousOn_termTSum.continuousWithinAt self_mem_Ici).tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun s : ℝ ↦ 1 - s * ZetaAsymptotics.termTSum s)
      (𝓝[>] 1) (𝓝 (1 - 1 * ZetaAsymptotics.termTSum 1)) :=
    tendsto_const_nhds.sub (hid.mul hcells)
  have hvalue : 1 - 1 * ZetaAsymptotics.termTSum 1 = Real.eulerMascheroniConstant := by
    rw [hat]
    ring
  rw [hvalue] at hlim
  apply ((Complex.continuous_ofReal.tendsto _).comp hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change ((1 - s * ZetaAsymptotics.termTSum s : ℝ) : ℂ) = _
  rw [← real_dirichlet_finite_part_eq_cells hs]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    sub_left_inj, Complex.ofReal_tsum]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  congr 1 with n
  rw [Complex.ofReal_cpow (by positivity)]
  norm_cast

/-- A function holomorphic away from a simple pole of residue one admits a
finite part there. Its real right limit determines the complex value. -/
theorem finitePart_limit_of_residue_and_real_limit (g : ℂ → ℂ) (a : ℂ)
    (hhol : ∀ {s : ℂ}, s ≠ 1 → DifferentiableAt ℂ g s)
    (hres : Tendsto (fun s : ℂ => (s - 1) * g s) (𝓝[≠] 1) (𝓝 1))
    (hright : Tendsto (fun s : ℝ => g s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 a)) :
    Tendsto (fun s : ℂ => g s - 1 / (s - 1)) (𝓝[≠] 1) (𝓝 a) := by
  -- The punctured little-o calculation generalizes the residue argument in
  -- Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean, copyright (c) 2024 David
  -- Loeffler, authors David Loeffler and Terence Tao, Apache License 2.0.
  let f (s : ℂ) := g s - 1 / (s - 1)
  suffices ∃ C, Tendsto f (𝓝[≠] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices hreal : Tendsto (fun s : ℝ => f s) (𝓝[>] 1) (𝓝 C) by
      exact (tendsto_nhds_unique hreal hright) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [mem_compl_singleton_iff, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact ne_of_gt ht
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (hhol hs).sub ((differentiableAt_const _).div ?_ ?_)
    · exact differentiableAt_id.sub_const 1
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero, sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : ℂ) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply hres.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with z hz
        field [sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz)]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _

/-- The real cell-sum calibration fixes the constant term of the zeta pole. -/
theorem finitePart_limit : Tendsto (fun s : ℂ => riemannZeta s - 1 / (s - 1))
    (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
  finitePart_limit_of_residue_and_real_limit riemannZeta _
    differentiableAt_riemannZeta riemannZeta_residue_one
    HVRNativeZetaPoleEquality.zeta_finite_part_tendsto_real_right

/-- At each ordinary point, the additive regularizer is locally the zeta
function minus the reciprocal of the linear pole factor. -/
theorem differentiableAt_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta₀ s := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    differentiableAt_id.sub_const 1
  have hreg : DifferentiableAt ℂ (fun z : ℂ => riemannZeta z - (z - 1)⁻¹) s :=
    (differentiableAt_riemannZeta hs).fun_sub (hlin.fun_inv (sub_ne_zero.mpr hs))
  apply hreg.congr_of_eventuallyEq
  filter_upwards [compl_singleton_mem_nhds hs] with z hz
  simp only [riemannZeta₀, if_neg (mem_compl_singleton_iff.mp hz)]

/-- The prescribed value at one is the punctured limit of the additive
regularizer. -/
theorem continuousAt_one : ContinuousAt riemannZeta₀ (1 : ℂ) := by
  rw [continuousAt_iff_punctured_nhds]
  have hval : riemannZeta₀ 1 = (Real.eulerMascheroniConstant : ℂ) := by
    simp [riemannZeta₀]
  rw [hval]
  apply finitePart_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [riemannZeta₀, if_neg (mem_compl_singleton_iff.mp hz), one_div]

/-- The completed additive regularizer is entire. -/
theorem additive_regularizer_differentiable : Differentiable ℂ riemannZeta₀ := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (f := riemannZeta₀) (c := 1) ?_ continuousAt_one).differentiableAt
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact differentiableAt_of_ne_one (mem_compl_singleton_iff.mp hz)
  · exact differentiableAt_of_ne_one hs

/-- Product rule for the entire factor `1 + (s - 1) * riemannZeta₀ s`. -/
theorem regularized_hasDerivAt (s : ℂ) :
    HasDerivAt riemannZeta₁ (riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s) s := by
  have hdiff : Differentiable ℂ riemannZeta₁ := by
    intro z
    unfold riemannZeta₁
    apply (differentiableAt_const_add_iff 1).mpr
    exact (differentiableAt_id.sub_const 1).fun_mul (additive_regularizer_differentiable z)
  have hd : deriv riemannZeta₁ s = riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s := by
    unfold riemannZeta₁
    rw [deriv_const_add, deriv_fun_mul (by fun_prop) (additive_regularizer_differentiable s)]
    simp
  rw [← hd]
  exact (hdiff s).hasDerivAt

theorem regularized_differentiable : Differentiable ℂ riemannZeta₁ :=
  fun s => (regularized_hasDerivAt s).differentiableAt

theorem regularized_value_one : riemannZeta₁ 1 = 1 := by
  simp only [riemannZeta₁, sub_self, zero_mul, add_zero]

/-- At the pole the linear factor cancels the additive regularizer's derivative. -/
theorem regularized_derivative_one : deriv riemannZeta₁ (1 : ℂ) = (Real.eulerMascheroniConstant : ℂ) := by
  simpa only [sub_self, zero_mul, add_zero, riemannZeta₀, if_pos rfl, if_true] using
    (regularized_hasDerivAt 1).deriv

/-- Off the pole, undo both regularizations using their definitions. -/
theorem regularized_div_sub_one {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s / (s - 1) = riemannZeta s := by
  simp only [riemannZeta₁, riemannZeta₀, if_neg hs]
  field_simp [sub_ne_zero.mpr hs] <;> ring

/-- Away from one the quotient of the entire regularized factor by the
linear factor agrees locally with the actual zeta function. -/
theorem quotient_eventually_eq_zeta {s : ℂ} (hs : s ≠ 1) :
    (fun z : ℂ => riemannZeta₁ z / (z - 1)) =ᶠ[𝓝 s] riemannZeta := by
  filter_upwards [compl_singleton_mem_nhds hs] with z hz
  exact regularized_div_sub_one (Set.mem_compl_singleton_iff.mp hz)

/-- The actual zeta function is analytic at each point other than one. -/
theorem zeta_analyticAt {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  have hquot : AnalyticAt ℂ (fun z : ℂ => riemannZeta₁ z / (z - 1)) s :=
    (regularized_differentiable.analyticAt s).div hlin (sub_ne_zero.mpr hs)
  exact hquot.congr (quotient_eventually_eq_zeta hs)

/-- Differentiation of u(z)/(z−1) on a neighborhood disjoint from one. -/
theorem zeta_derivative_of_regularized_quotient {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s =
      -((s - 1)⁻¹) ^ 2 * riemannZeta₁ s + (s - 1)⁻¹ * deriv riemannZeta₁ s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hf := quotient_eventually_eq_zeta hs
  have hlin : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hd := ((regularized_differentiable s).hasDerivAt.fun_div hlin hsub).deriv
  rw [← hf.deriv_eq, hd]
  field_simp [hsub] <;> ring

/-- Pointwise logarithmic-derivative identity from the derivative of a quotient. -/
theorem log_derivative_eq {s : ℂ} (hs : s ≠ 1)
    (hreg : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  rw [zeta_derivative_of_regularized_quotient hs, ← regularized_div_sub_one hs]
  field_simp [sub_ne_zero.mpr hs, hreg] <;> ring

/-- Nonvanishing of the regularized factor near its unit value. -/
theorem regularized_eventually_ne : ∀ᶠ s : ℂ in 𝓝 1, riemannZeta₁ s ≠ 0 :=
  (regularized_differentiable 1).continuousAt.tendsto.eventually_ne
    (regularized_value_one.trans_ne one_ne_zero)

/-- The pointwise identity holds on a punctured neighborhood of the pole. -/
theorem log_derivative_eventually_eq :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ),
      deriv riemannZeta s / riemannZeta s =
        - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  filter_upwards [self_mem_nhdsWithin, regularized_eventually_ne.filter_mono nhdsWithin_le_nhds] with s hs hreg
  exact log_derivative_eq (Set.mem_compl_singleton_iff.mp hs) hreg

end HVRNativeZetaPoleEquality
