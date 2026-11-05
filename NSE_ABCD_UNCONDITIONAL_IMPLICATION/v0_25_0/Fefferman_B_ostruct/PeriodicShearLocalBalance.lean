import PeriodicShearFlux

noncomputable section
open Fefferman.ConcreteReal
open scoped BigOperators

namespace CondFeffB

private theorem flux_dx_mul (j : Fin 3) {f g : RSpace → ℝ} {x : RSpace}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spatialDerivative j (fun y => f y * g y) x =
      f x * spatialDerivative j g x + g x * spatialDerivative j f x := by
  simp only [spatialDerivative, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem flux_dx_const_mul (j : Fin 3) (c : ℝ) {f : RSpace → ℝ} {x : RSpace}
    (hf : DifferentiableAt ℝ f x) :
    spatialDerivative j (fun y => c * f y) x = c * spatialDerivative j f x := by
  simp only [spatialDerivative, fderiv_const_mul hf c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

private theorem flux_dx_sub (j : Fin 3) {f g : RSpace → ℝ} {x : RSpace}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spatialDerivative j (fun y => f y - g y) x =
      spatialDerivative j f x - spatialDerivative j g x := by
  simp only [spatialDerivative, fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

private theorem flux_dx_sum (j : Fin 3) {A : Fin 3 → RSpace → ℝ} {x : RSpace}
    (h : ∀ i, DifferentiableAt ℝ (A i) x) :
    spatialDerivative j (fun y => ∑ i, A i y) x =
      ∑ i, spatialDerivative j (A i) x := by
  simp only [spatialDerivative,
    fderiv_fun_sum (u := Finset.univ) (A := A) (fun i _ => h i),
    ContinuousLinearMap.sum_apply]

set_option maxHeartbeats 800000 in
/-- Product differentiation of the j-th energy flux on an actual spatial slice. -/
theorem spatialDerivative_differenceFlux (ν : ℝ) (U W : RSpace → RVector)
    (P : RSpace → ℝ) (x : RSpace) (j : Fin 3)
    (hU : DifferentiableAt ℝ (fun y => U y j) x)
    (hW : ∀ i, DifferentiableAt ℝ (fun y => W y i) x)
    (hDW : ∀ i, DifferentiableAt ℝ (spatialDerivative j (fun y => W y i)) x)
    (hP : DifferentiableAt ℝ P x) :
    spatialDerivative j (fun y => differenceFlux ν U W P y j) x =
      fluxDerivativeTerm ν (U x) (W x) (P x)
        (fun k i => spatialDerivative k (fun y => U y i) x)
        (fun k i => spatialDerivative k (fun y => W y i) x)
        (fun k i => spatialDerivative k (spatialDerivative k (fun y => W y i)) x)
        (fun k => spatialDerivative k P x) j := by
  let g : Fin 3 → RSpace → ℝ := fun i => spatialDerivative j (fun y => W y i)
  let a : RSpace → ℝ := fun y => ∑ i, W y i * g i y
  let b : RSpace → ℝ := fun y => ∑ i, W y i ^ 2
  have hg (i : Fin 3) : DifferentiableAt ℝ (g i) x := hDW i
  have ha : DifferentiableAt ℝ a x :=
    DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun (i : Fin 3) (y : RSpace) => W y i * g i y)
      (fun i _ => (hW i).fun_mul (hg i))
  have hb : DifferentiableAt ℝ b x :=
    DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun (i : Fin 3) (y : RSpace) => W y i ^ 2) (fun i _ => (hW i).fun_pow 2)
  have da : spatialDerivative j a x =
      ∑ i, (g i x ^ 2 + W x i * spatialDerivative j (g i) x) := by
    change spatialDerivative j (fun y => ∑ i, W y i * g i y) x = _
    rw [flux_dx_sum j (A := fun i y => W y i * g i y)
      (fun i => (hW i).fun_mul (hg i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [flux_dx_mul j (hW i) (hg i)]
    dsimp only [g]
    ring
  have db : spatialDerivative j b x =
      ∑ i, 2 * W x i * spatialDerivative j (fun y => W y i) x := by
    change spatialDerivative j (fun y => ∑ i, W y i ^ 2) x = _
    rw [flux_dx_sum j (A := fun i y => W y i ^ 2)
      (fun i => (hW i).fun_pow 2)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_two]
    rw [flux_dx_mul j (hW i) (hW i)]
    ring
  change spatialDerivative j (fun y => (2 * ν * a y - U y j * b y)
    - 2 * P y * W y j) x = _
  rw [flux_dx_sub j ((ha.const_mul (2 * ν)).fun_sub (hU.fun_mul hb))
        ((hP.const_mul 2).fun_mul (hW j)),
    flux_dx_sub j (ha.const_mul (2 * ν)) (hU.fun_mul hb),
    flux_dx_const_mul j (2 * ν) ha, flux_dx_mul j hU hb,
    flux_dx_mul j (hP.const_mul 2) (hW j), flux_dx_const_mul j 2 hP,
    da, db]
  dsimp only [fluxDerivativeTerm, a, b, g]
  ring

theorem fluxDivergence_differenceFlux (ν : ℝ) (U W : RSpace → RVector)
    (P : RSpace → ℝ) (x : RSpace)
    (hU : ∀ j, DifferentiableAt ℝ (fun y => U y j) x)
    (hW : ∀ i, DifferentiableAt ℝ (fun y => W y i) x)
    (hDW : ∀ j i, DifferentiableAt ℝ (spatialDerivative j (fun y => W y i)) x)
    (hP : DifferentiableAt ℝ P x) :
    fluxDivergence (differenceFlux ν U W P) x =
      ∑ j, fluxDerivativeTerm ν (U x) (W x) (P x)
        (fun k i => spatialDerivative k (fun y => U y i) x)
        (fun k i => spatialDerivative k (fun y => W y i) x)
        (fun k i => spatialDerivative k (spatialDerivative k (fun y => W y i)) x)
        (fun k => spatialDerivative k P x) j := by
  unfold fluxDivergence
  apply Finset.sum_congr rfl
  intro j _
  exact spatialDerivative_differenceFlux ν U W P x j (hU j) hW (hDW j) hP

end CondFeffB
