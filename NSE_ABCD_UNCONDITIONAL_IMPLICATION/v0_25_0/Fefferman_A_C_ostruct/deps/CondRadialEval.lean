import CondRadial
import CondSeries
import CondGaussian

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
open scoped ContDiff
noncomputable section

local notation "D" => spatialDerivative
local notation "q" => normSq3

private lemma radial_q_smooth : ContDiff ℝ ⊤ q := by unfold normSq3; fun_prop

private lemma radial_partial_coord (i j : Fin 3) (x : RSpace) :
    D i (fun y : RSpace => y j) x = basisDirection i j := by
  unfold spatialDerivative
  rw [(hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv] <;> rfl

private lemma radial_partial_mul (i : Fin 3) (f g : RSpace → ℝ) (x : RSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D i (fun y => f y * g y) x = f x * D i g x + g x * D i f x := by
  simp only [spatialDerivative, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma radial_partial_q (i : Fin 3) (x : RSpace) : D i q x = 2 * x i := by
  have square (j : Fin 3) :
      D i (fun y : RSpace => y j * y j) x = x j * basisDirection i j + x j * basisDirection i j := by
    rw [radial_partial_mul i (fun y : RSpace => y j) (fun y : RSpace => y j) x
      (by fun_prop) (by fun_prop), radial_partial_coord]
  change D i (fun y : RSpace => (y 0*y 0+y 1*y 1)+y 2*y 2) x = _
  rw [partial_add (f := fun y : RSpace => y 0*y 0+y 1*y 1)
      (g := fun y : RSpace => y 2*y 2) (by fun_prop) (by fun_prop),
    partial_add (f := fun y : RSpace => y 0*y 0) (g := fun y : RSpace => y 1*y 1)
      (by fun_prop) (by fun_prop), square 0, square 1, square 2]
  fin_cases i
  · change (x 0 * 1 + x 0 * 1) + (x 1 * 0 + x 1 * 0) +
        (x 2 * 0 + x 2 * 0) = 2 * x 0
    ring
  · change (x 0 * 0 + x 0 * 0) + (x 1 * 1 + x 1 * 1) +
        (x 2 * 0 + x 2 * 0) = 2 * x 1
    ring
  · change (x 0 * 0 + x 0 * 0) + (x 1 * 0 + x 1 * 0) +
        (x 2 * 1 + x 2 * 1) = 2 * x 2
    ring

private lemma radial_partial_comp (G : ℝ → ℝ) (hG : Differentiable ℝ G)
    (i : Fin 3) (x : RSpace) :
    D i (G ∘ q) x = (2 * x i) * deriv G (q x) := by
  unfold spatialDerivative
  rw [fderiv_comp x (hG (q x)) (radial_q_smooth.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul]
  change D i q x * deriv G (q x) = _
  rw [radial_partial_q]

private lemma smooth_ordinary_deriv {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (deriv G) := (contDiff_infty_iff_deriv.mp hG).2

/-- Scalar radial Laplacian, in the variable s=|x|². -/
private def radialOperator (G : ℝ → ℝ) (s : ℝ) : ℝ :=
  4*s*iteratedDeriv 2 G s + 6*iteratedDeriv 1 G s

private lemma smooth_it {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k hG

private lemma radialOperator_smooth {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (radialOperator G) :=
  (((contDiff_const.mul contDiff_id).mul (smooth_it hG 2))).add
    (contDiff_const.mul (smooth_it hG 1))

private lemma radial_diag {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (i : Fin 3) (x : RSpace) :
    D i (D i (G ∘ q)) x =
      2 * deriv G (q x) + 4 * (x i)^2 * deriv (deriv G) (q x) := by
  have h1 : D i (G ∘ q) =
      (fun y : RSpace => (y i + y i) * (deriv G ∘ q) y) := by
    funext y
    rw [radial_partial_comp G (hG.differentiable (by simp))]
    simp only [Function.comp_apply]
    ring
  have d_coord : D i (fun y : RSpace => y i + y i) x = 2 := by
    rw [partial_add (f := fun y : RSpace => y i) (g := fun y : RSpace => y i)
        (by fun_prop) (by fun_prop), radial_partial_coord]
    norm_num [basisDirection]
  rw [h1, radial_partial_mul i (fun y : RSpace => y i + y i) (deriv G ∘ q) x
      (by fun_prop) (((smooth_ordinary_deriv hG).differentiable (by simp)).comp
        (radial_q_smooth.differentiable (by simp)) x),
    radial_partial_comp (deriv G) ((smooth_ordinary_deriv hG).differentiable (by simp)), d_coord]
  simp only [Function.comp_apply]
  ring

private lemma physical_radial_laplacian {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    laplacian realAnalysis (G ∘ q) = radialOperator G ∘ q := by
  funext x
  change D 0 (D 0 (G ∘ q)) x + D 1 (D 1 (G ∘ q)) x + D 2 (D 2 (G ∘ q)) x =
    radialOperator G (q x)
  rw [radial_diag hG, radial_diag hG, radial_diag hG]
  have firstD : iteratedDeriv 1 G = deriv G := iteratedDeriv_one
  have secondD : iteratedDeriv 2 G = deriv (deriv G) := by
    rw [show 2 = 1+1 by decide, iteratedDeriv_succ, firstD]
  simp only [radialOperator, firstD, secondD]
  generalize hs : deriv G (q x) = u
  generalize ht : deriv (deriv G) (q x) = v
  unfold normSq3
  ring

private lemma iterated_radialOperator {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) :
    iteratedDeriv k (radialOperator G) =
      fun s => 4*s*iteratedDeriv (k+2) G s + (4*(k:ℝ)+6)*iteratedDeriv (k+1) G s := by
  have jet (j : ℕ) (s : ℝ) :
      HasDerivAt (iteratedDeriv j G) (iteratedDeriv (j+1) G s) s := by
    rw [iteratedDeriv_succ]
    exact ((smooth_it hG j).differentiable (by simp) s).hasDerivAt
  induction k with
  | zero =>
    funext s
    simp only [iteratedDeriv_zero, radialOperator, Nat.zero_add, Nat.cast_zero, mul_zero, zero_add]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have hlin : HasDerivAt (fun t : ℝ => 4*t) 4 s := by
      simpa using (hasDerivAt_id s).const_mul (4 : ℝ)
    calc
      deriv (fun t : ℝ => 4*t*iteratedDeriv (k+2) G t +
          (4*(k:ℝ)+6)*iteratedDeriv (k+1) G t) s =
          4*iteratedDeriv (k+2) G s + 4*s*iteratedDeriv (k+3) G s +
            (4*(k:ℝ)+6)*iteratedDeriv (k+2) G s :=
        ((hlin.mul (jet (k+2) s)).add ((jet (k+1) s).const_mul (4*(k:ℝ)+6))).deriv
      _ = 4*s*iteratedDeriv (k+3) G s +
          (4*(k.succ:ℝ)+6)*iteratedDeriv (k+2) G s := by
        rw [Nat.cast_succ]
        ring

private def normalizedJet (G : ℝ → ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k G 0 / (k.factorial : ℝ)

private lemma normalized_radialOperator {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    normalizedJet (radialOperator G) = CondPoly.radialDelta (normalizedJet G) := by
  funext k
  simp only [normalizedJet, iterated_radialOperator hG, mul_zero, zero_mul, zero_add,
    CondPoly.radialDelta, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hfac,hk] <;> ring

private lemma scalarHeat_succ_inner (n : ℕ) (f : RSpace → ℝ) :
    scalarHeat (n+1) f = scalarHeat n (laplacian realAnalysis f) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (laplacian realAnalysis) ih

private lemma scalarHeat_at_origin {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    scalarHeat n (G ∘ q) 0 = CondPoly.radialDeltaIter n (normalizedJet G) 0 := by
  induction n generalizing G with
  | zero => simp [scalarHeat, CondPoly.radialDeltaIter, normalizedJet, normSq3]
  | succ n ih =>
    rw [scalarHeat_succ_inner, physical_radial_laplacian hG, ih (radialOperator_smooth hG),
      normalized_radialOperator hG] <;> rfl

/-- Transfer the normalized derivatives at zero from the scalar analytic germ
to any smooth extension agreeing with it on the closed positive ray. -/
private lemma normalized_extension {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (same : ∀ s : ℝ, 0 ≤ s → G s = Real.exp (-s) / (1+s)) :
    normalizedJet G = CondPoly.radialCoeff := by
  let g := fun s : ℝ => Real.exp (-s) / (1+s)
  have hg : AnalyticAt ℝ g 0 := radial_hasFPowerSeriesAt.analyticAt
  have hp := hg.hasFPowerSeriesAt.eq_formalMultilinearSeries radial_hasFPowerSeriesAt
  have coeffEq : (fun j => iteratedDeriv j g 0 / (j.factorial : ℝ)) = CondPoly.radialCoeff :=
    FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ hp
  funext k
  have heq : Set.EqOn G g (Set.Ici 0) := fun s hs => same s hs
  have hk : (k : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤)
  have hGk : ContDiffAt ℝ (k : ℕ∞ω) G 0 := (hG.of_le hk).contDiffAt
  have hj : iteratedDeriv k G 0 = iteratedDeriv k g 0 := by
    calc
      iteratedDeriv k G 0 = iteratedDerivWithin k G (Set.Ici 0) 0 :=
        (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hGk (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)).symm
      _ = iteratedDerivWithin k g (Set.Ici 0) 0 := iteratedDerivWithin_congr heq (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)
      _ = iteratedDeriv k g 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hg.contDiffAt (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)
  rw [normalizedJet, hj]
  exact congrFun coeffEq k

/-- All scalar radial heat jets of the original three-dimensional datum. -/
theorem concrete_scalar_heat_at_origin (n : ℕ) :
    scalarHeat n psi 0 = CondPoly.radialDeltaIter n CondPoly.radialCoeff 0 := by
  obtain ⟨G, same⟩ := CondGaussian.exists_scalar_extension
  have gpsi : psi = ((G : ℝ → ℝ) ∘ q) := by
    funext x
    change Real.exp (-(q x)) / (1+q x) = G (q x)
    exact (same (q x) (by
      unfold normSq3
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)])).symm
  have hG : ContDiff ℝ ∞ (G : ℝ → ℝ) := G.smooth'
  calc
    scalarHeat n psi 0 = scalarHeat n ((G : ℝ → ℝ) ∘ q) 0 :=
      congrArg (fun f : RSpace → ℝ => scalarHeat n f 0) gpsi
    _ = CondPoly.radialDeltaIter n (normalizedJet (G : ℝ → ℝ)) 0 :=
      scalarHeat_at_origin (G := (G : ℝ → ℝ)) hG n
    _ = CondPoly.radialDeltaIter n CondPoly.radialCoeff 0 :=
      congrArg (fun a : ℕ → ℝ => CondPoly.radialDeltaIter n a 0)
        (normalized_extension (G := (G : ℝ → ℝ)) hG same)

theorem concrete_scalar_radial_heat_extraction : ScalarRadialHeatExtraction :=
  fun n => concrete_scalar_heat_at_origin (n+1)

end
end CondFeffA

#print axioms CondFeffA.concrete_scalar_heat_at_origin
#print axioms CondFeffA.concrete_scalar_radial_heat_extraction
