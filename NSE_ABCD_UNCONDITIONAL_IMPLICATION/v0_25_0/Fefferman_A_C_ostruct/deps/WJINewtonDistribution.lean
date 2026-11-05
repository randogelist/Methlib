import WJINewtonPoissonTest
import WJINewtonSmooth
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory Filter WJISmooth
open scoped BigOperators ContDiff
noncomputable section

local notation "D" => spatialDerivative
local notation "L" => laplacian realAnalysis

private theorem kernel_norm (z : RSpace) : ‖newtonKernel z‖ = newtonKernel z := by
  apply Real.norm_of_nonneg
  exact inv_nonneg.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg _))

private theorem kernel_even (z : RSpace) : newtonKernel (-z) = newtonKernel z := by
  have he : normSq3 (-z) = normSq3 z := by simp [normSq3, Pi.neg_apply]
  simp only [newtonKernel, euclideanNorm3, he]

private theorem kernel_sub_comm (x y : RSpace) : newtonKernel (x-y) = newtonKernel (y-x) := by
  simpa only [neg_sub] using kernel_even (y-x)

private theorem potential_mul (f : RSpace → ℝ) (x : RSpace) :
    newtonPotential f x = ∫ y, f y * newtonKernel (x-y) := by
  simp only [newtonPotential, newtonKernel, div_eq_mul_inv]

/-- Self-adjointness of the literal Newton integral when the source is
    bounded and integrable and the other scalar is integrable. -/
theorem wji_newton_pairing_swap (g η : RSpace → ℝ) (hg : Measurable g)
    (hi : Integrable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M)
    (hη : Measurable η) (hiη : Integrable η) :
    (∫ x, η x * newtonPotential g x) = ∫ y, g y * newtonPotential η y := by
  let F (x y : RSpace) := η x * (g y * newtonKernel (x-y))
  let B := M * newtonLocalMass 1 + ∫ y, ‖g y‖
  have hfm : Measurable (Function.uncurry F) :=
    (hη.comp measurable_fst).mul ((hg.comp measurable_snd).mul
      (newtonKernel_measurable.comp (measurable_fst.sub measurable_snd)))
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure RSpace).prod volume) := hfm.aemeasurable.aestronglyMeasurable
  have inner (x : RSpace) : Integrable (F x) :=
    (integrable_newton_majorized (k := 1) (by decide) newtonKernel_measurable
      newtonKernel_majorized hi hb x).const_mul (η x)
  have bound (x : RSpace) : (∫ y, ‖g y‖ * newtonKernel (x-y)) ≤ B := by
    apply (Real.le_norm_self _).trans
    simpa only [norm_norm] using
      (integral_newton_majorized_le (k := 1) (by decide) newtonKernel_measurable
        newtonKernel_majorized hi.norm (fun y => by simpa only [norm_norm] using hb y) x)
  have hprod : Integrable (Function.uncurry F) ((volume : Measure RSpace).prod volume) := by
    apply (integrable_prod_iff hmeas).mpr
    refine ⟨Eventually.of_forall inner, ?_⟩
    apply (hiη.norm.mul_const B).mono' hmeas.norm.integral_prod_right'
    apply Eventually.of_forall
    intro x
    change ‖∫ y, ‖F x y‖‖ ≤ ‖η x‖ * B
    have hnonneg : 0 ≤ ∫ y, ‖F x y‖ :=
      integral_nonneg (f := fun y : RSpace => ‖F x y‖) (fun y => norm_nonneg (F x y))
    rw [Real.norm_of_nonneg hnonneg]
    calc
      (∫ y, ‖F x y‖) = ‖η x‖ * (∫ y, ‖g y‖ * newtonKernel (x-y)) := by
        simp only [F, norm_mul, kernel_norm, integral_const_mul]
      _ ≤ ‖η x‖ * B := mul_le_mul_of_nonneg_left (bound x) (norm_nonneg _)
  calc
    (∫ x, η x * newtonPotential g x) = ∫ x, ∫ y, F x y := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change η x * newtonPotential g x = ∫ y, F x y
      rw [potential_mul g x]
      exact (integral_const_mul (η x) (fun y : RSpace => g y * newtonKernel (x-y))).symm
    _ = ∫ y, ∫ x, F x y := integral_integral_swap (f := F) hprod
    _ = ∫ y, g y * newtonPotential η y := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change (∫ x, F x y) = g y * newtonPotential η y
      rw [potential_mul η y, ← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      change η x * (g y * newtonKernel (x-y)) = g y * (η x * newtonKernel (y-x))
      rw [kernel_sub_comm x y]
      ring

private theorem partial_shift (f : RSpace → ℝ) (a : RSpace) (j : Fin 3) :
    D j (fun z => f (a+z)) = fun z => D j f (a+z) := by
  funext z
  exact congrArg (fun A : RSpace →L[ℝ] ℝ => A (basisDirection j))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := f) (x := z) a)

private theorem lap_shift (f : RSpace → ℝ) (a z : RSpace) :
    L (fun y => f (a+y)) z = L f (a+z) := by
  have h (j : Fin 3) : D j (D j (fun y => f (a+y))) z = D j (D j f) (a+z) := by
    rw [partial_shift f a j, partial_shift (D j f) a j]
  change D 0 (D 0 (fun y => f (a+y))) z + D 1 (D 1 (fun y => f (a+y))) z +
      D 2 (D 2 (fun y => f (a+y))) z = _
  rw [h 0, h 1, h 2] <;> rfl

/-- Translation of the compact fundamental identity away from zero. -/
theorem wji_newton_of_compact_lap (φ : RSpace → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    newtonPotential (L φ) = -φ := by
  funext x
  let h (z : RSpace) := φ (x+z)
  have hreg : ContDiff ℝ ∞ h := hφ.comp (contDiff_const.add contDiff_id)
  have hcomp : HasCompactSupport h := hc.comp_homeomorph (Homeomorph.addLeft x)
  have hfund := wji_newton_fundamental_test hreg hcomp
  have hx : -(newtonPotential (L φ) x) = φ x := by
    calc
      _ = ∫ y, -((L φ y) * newtonKernel (x-y)) := by rw [integral_neg, potential_mul]
      _ = ∫ z, -((L φ (x+z)) * newtonKernel (x-(x+z))) :=
        (integral_add_left_eq_self (μ := volume)
          (fun y => -((L φ y) * newtonKernel (x-y))) x).symm
      _ = ∫ z, newtonKernel z * (-(L h z)) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro z
        have he : L h z = L φ (x+z) := lap_shift φ x z
        change -((L φ (x+z)) * newtonKernel (x-(x+z))) = newtonKernel z * (-(L h z))
        rw [he, show x-(x+z) = -z by abel, kernel_even]
        ring
      _ = φ x := by simpa only [h, add_zero] using hfund
  change newtonPotential (L φ) x = -φ x
  linarith only [hx]

private lemma partial_smooth {f : RSpace → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (D i f) := (partialMap i (⟨f, hf⟩ : scalarSpace)).property

private lemma lap_smooth {f : RSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (L f) :=
  ((partial_smooth (partial_smooth hf 0) 0).add (partial_smooth (partial_smooth hf 1) 1)).add
    (partial_smooth (partial_smooth hf 2) 2)

private lemma partial_compact {f : RSpace → ℝ} (hc : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (D i f) := hc.fderiv_apply ℝ (basisDirection i)

private lemma lap_compact {f : RSpace → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (L f) :=
  ((partial_compact (partial_compact hc 0) 0).add (partial_compact (partial_compact hc 1) 1)).add
    (partial_compact (partial_compact hc 2) 2)

private lemma prod_integrable {f q : RSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport f) : Integrable (fun x => f x * q x) :=
  (hf.continuous.mul hq.continuous).integrable_of_hasCompactSupport hc.mul_right

private lemma compact_ibp {f q : RSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport f) (j : Fin 3) :
    (∫ x, f x * D j q x) = -(∫ x, D j f x * q x) :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := q) (μ := volume) (v := basisDirection j)
    (prod_integrable (partial_smooth hf j) hq (partial_compact hc j))
    (prod_integrable hf (partial_smooth hq j) hc) (prod_integrable hf hq hc)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hq.differentiable (by simp) x)

private lemma lap_sum (f : RSpace → ℝ) (x : RSpace) :
    L f x = ∑ j : Fin 3, D j (D j f) x := by rw [Fin.sum_univ_three] <;> rfl

/-- Classical second-order integration by parts needs compact support only
    on the test field; the Newton potential itself may be nonintegrable. -/
theorem wji_laplacian_compact_test {φ q : RSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hq : ContDiff ℝ ∞ q) (hc : HasCompactSupport φ) :
    (∫ x, φ x * L q x) = ∫ x, L φ x * q x := by
  let A (j : Fin 3) (x : RSpace) := φ x * D j (D j q) x
  let B (j : Fin 3) (x : RSpace) := D j (D j φ) x * q x
  have hA (j : Fin 3) : Integrable (A j) := prod_integrable hφ (partial_smooth (partial_smooth hq j) j) hc
  have hB (j : Fin 3) : Integrable (B j) :=
    prod_integrable (partial_smooth (partial_smooth hφ j) j) hq (partial_compact (partial_compact hc j) j)
  have hdiag (j : Fin 3) : (∫ x, A j x) = ∫ x, B j x := by
    change (∫ x, φ x * D j (D j q) x) = ∫ x, D j (D j φ) x * q x
    rw [compact_ibp (f := φ) (q := D j q) hφ (partial_smooth hq j) hc j,
      compact_ibp (f := D j φ) (q := q) (partial_smooth hφ j) hq (partial_compact hc j) j,
      neg_neg]
  calc
    (∫ x, φ x * L q x) = ∫ x, ∑ j : Fin 3, A j x := by simp only [lap_sum q, Finset.mul_sum, A]
    _ = ∑ j : Fin 3, ∫ x, A j x := integral_finsetSum Finset.univ (f := A) (fun j _ => hA j)
    _ = ∑ j : Fin 3, ∫ x, B j x := Finset.sum_congr rfl (fun j _ => hdiag j)
    _ = ∫ x, ∑ j : Fin 3, B j x :=
      (integral_finsetSum Finset.univ (f := B) (fun j _ => hB j)).symm
    _ = ∫ x, L φ x * q x := by simp only [lap_sum φ, Finset.sum_mul, B]

/-- The weak Poisson equation is unconditional for bounded integrable
    sources. Differentiability or Sobolev membership of the potential is
    unnecessary at this stage. -/
theorem wji_newton_distributional_poisson {g : RSpace → ℝ} (hm : Measurable g)
    (hi : Integrable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M)
    (φ : RSpace → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, L φ x * newtonPotential g x) = ∫ x, φ x * (-g x) := by
  rw [wji_newton_pairing_swap g (L φ) hm hi hb (lap_smooth hφ).continuous.measurable
      ((lap_smooth hφ).continuous.integrable_of_hasCompactSupport (lap_compact hc)),
    wji_newton_of_compact_lap φ hφ hc]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change g x * (-φ x) = φ x * (-g x)
  ring

/-- The compact fundamental identity determines the actual scalar Laplacian
    of the Newton potential for a global smooth bounded L¹ source. -/
theorem wji_newton_poisson_smooth_source {g : RSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hi : Integrable g) {M : ℝ} (hb : ∀ x, ‖g x‖ ≤ M)
    (hq : ContDiff ℝ ∞ (newtonPotential g)) : L (newtonPotential g) = -g := by
  have hc := (lap_smooth hq).continuous
  have hc' : Continuous (-g) := hg.continuous.neg
  refine MeasureTheory.Measure.eq_of_ae_eq (μ := (volume : Measure RSpace)) ?_ hc hc'
  refine ae_eq_of_integral_contDiff_smul_eq (μ := (volume : Measure RSpace))
    (f := L (newtonPotential g)) (f' := -g) hc.locallyIntegrable hc'.locallyIntegrable ?_
  intro φ hφ hφc
  change (∫ x, φ x * L (newtonPotential g) x) = ∫ x, φ x * (-g x)
  calc
    _ = ∫ x, L φ x * newtonPotential g x := wji_laplacian_compact_test hφ hq hφc
    _ = _ := wji_newton_distributional_poisson hg.continuous.measurable hi hb φ hφ hφc

/-- Once the actual Newton gradient belongs to the all-order Sobolev space,
    the signed Poisson equality follows without a separate hypothesis. -/
theorem wji_newtonPoisson_of_gradient_mem
    (hG : ∀ v w : WJISobolev.space,
      wjiScalarGradient (wjiNewtonScalar v.val w.val) ∈ WJISobolev.space) : NewtonPoissonOn := by
  intro v w
  refine ⟨hG v w, ?_⟩
  let g := fieldDiv (transport v.val w.val)
  have ht := WJISobolev.transport_mem v w
  have hd (i : Fin 3) := WJISobolev.scalar_partial (ht i) i
  have hs : g ∈ WJISobolev.scalar :=
    WJISobolev.scalar.add_mem (WJISobolev.scalar.add_mem (hd 0) (hd 1)) (hd 2)
  obtain ⟨M, hb⟩ := WJISobolev.transport_div_bounded v w
  exact wji_newton_poisson_smooth_source (g := g) (WJISobolev.scalar_smooth hs)
    (WJISobolev.transport_div_integrable v w) hb
    (wji_smooth_of_gradient_mem (wjiNewtonScalar_differentiable v w) (hG v w))

end
end CondFeffA

#print axioms CondFeffA.wji_newton_pairing_swap
#print axioms CondFeffA.wji_newton_of_compact_lap
#print axioms CondFeffA.wji_laplacian_compact_test
#print axioms CondFeffA.wji_newton_distributional_poisson
#print axioms CondFeffA.wji_newton_poisson_smooth_source
#print axioms CondFeffA.wji_newtonPoisson_of_gradient_mem
