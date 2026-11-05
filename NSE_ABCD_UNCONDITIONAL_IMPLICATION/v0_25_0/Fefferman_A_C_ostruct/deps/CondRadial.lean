import CondRecurrence
import CondPoly

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
noncomputable section

local notation "D" => spatialDerivative
local notation "L" => laplacian realAnalysis

/-- The actual scalar iterates of the three-dimensional spatial Laplacian. -/
def scalarHeat : ℕ → (RSpace → ℝ) → RSpace → ℝ
  | 0, f => f
  | n + 1, f => L (scalarHeat n f)

theorem scalarHeat_eq_iterate (n : ℕ) (f : RSpace → ℝ) :
    scalarHeat n f = (laplacian realAnalysis)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [scalarHeat, Function.iterate_succ_apply', ih]

private theorem lap_analytic {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (L f) := by
  exact ((partial_analytic (partial_analytic hf 0) 0).add
    (partial_analytic (partial_analytic hf 1) 1)).add
    (partial_analytic (partial_analytic hf 2) 2)

private theorem scalarHeat_analytic {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) (n : ℕ) :
    ContDiff ℝ ⊤ (scalarHeat n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact lap_analytic ih

private theorem lap_add_fields {f g : RSpace → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    L (fun x => f x + g x) = fun x => L f x + L g x := by
  have move (i : Fin 3) (x : RSpace) :
      D i (D i (fun y => f y + g y)) x = D i (D i f) x + D i (D i g) x := by
    have he : D i (fun y => f y + g y) = fun y => D i f y + D i g y :=
      funext (partial_add hf hg i)
    rw [he]
    exact partial_add (partial_analytic hf i) (partial_analytic hg i) i x
  funext x
  change D 0 (D 0 _) x + D 1 (D 1 _) x + D 2 (D 2 _) x =
    (D 0 (D 0 f) x + D 1 (D 1 f) x + D 2 (D 2 f) x) +
    (D 0 (D 0 g) x + D 1 (D 1 g) x + D 2 (D 2 g) x)
  rw [move 0 x, move 1 x, move 2 x]
  ring

private theorem lap_partial_field {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    L (D i f) = D i (L f) := by
  let hdiag (j : Fin 3) := partial_analytic (partial_analytic hf j) j
  have move (j : Fin 3) (x : RSpace) :
      D j (D j (D i f)) x = D i (D j (D j f)) x := by
    have he : D j (D i f) = D i (D j f) := funext (partial_comm hf j i)
    rw [he]
    exact partial_comm (partial_analytic hf j) j i x
  funext x
  change D 0 (D 0 (D i f)) x + D 1 (D 1 (D i f)) x + D 2 (D 2 (D i f)) x =
    D i (fun y => D 0 (D 0 f) y + D 1 (D 1 f) y + D 2 (D 2 f) y) x
  rw [partial_add ((hdiag 0).add (hdiag 1)) (hdiag 2),
    partial_add (hdiag 0) (hdiag 1), move 0 x, move 1 x, move 2 x]

/-- Move the solenoidal profile's two transverse derivatives through all
of the physical heat iterates, as identities of fields. -/
theorem heat_first_as_transverse_hessian (n : ℕ) :
    (fun x => heatIterate n x 0) =
      fun x => D 1 (D 1 (scalarHeat n psi)) x + D 2 (D 2 (scalarHeat n psi)) x := by
  induction n with
  | zero => exact profile_first
  | succ n ih =>
    let f := scalarHeat n psi
    have hf : ContDiff ℝ ⊤ f := scalarHeat_analytic psi_analytic n
    change L (fun x => heatIterate n x 0) =
      fun x => D 1 (D 1 (L f)) x + D 2 (D 2 (L f)) x
    rw [ih]
    change L (fun x => D 1 (D 1 f) x + D 2 (D 2 f) x) = _
    rw [lap_add_fields (partial_analytic (partial_analytic hf 1) 1)
      (partial_analytic (partial_analytic hf 2) 2),
      lap_partial_field (partial_analytic hf 1) 1, lap_partial_field hf 1,
      lap_partial_field (partial_analytic hf 2) 2, lap_partial_field hf 2]

private def cycNext : Fin 3 → Fin 3 := ![1, 2, 0]
private def cycPrev : Fin 3 → Fin 3 := ![2, 0, 1]

private def cyc : RSpace →L[ℝ] RSpace :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (cycNext i)

private theorem cyc_basis (i : Fin 3) :
    cyc (basisDirection i) = basisDirection (cycPrev i) := by
  funext j
  change (if cycNext j = i then (1 : ℝ) else 0) = (if j = cycPrev i then 1 else 0)
  fin_cases i <;> fin_cases j <;> rfl

private theorem partial_cyc {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    D i (fun y => f (cyc y)) = fun y => D (cycPrev i) f (cyc y) := by
  funext x
  have hcomp := ((hf.differentiable (by simp) (cyc x)).hasFDerivAt).comp x cyc.hasFDerivAt
  calc
    (fderiv ℝ (f ∘ (cyc : RSpace → RSpace)) x) (basisDirection i) =
        (fderiv ℝ f (cyc x)) (cyc (basisDirection i)) :=
      congrArg (fun A : RSpace →L[ℝ] ℝ => A (basisDirection i)) hcomp.fderiv
    _ = (fderiv ℝ f (cyc x)) (basisDirection (cycPrev i)) :=
      congrArg (fun v : RSpace => (fderiv ℝ f (cyc x)) v) (cyc_basis i)

private theorem diag_cyc {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    D i (D i (fun y => f (cyc y))) = fun y => D (cycPrev i) (D (cycPrev i) f) (cyc y) := by
  rw [partial_cyc hf i]
  exact partial_cyc (partial_analytic hf (cycPrev i)) i

private theorem lap_cyc {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) :
    L (fun y => f (cyc y)) = fun y => L f (cyc y) := by
  funext x
  change D 0 (D 0 _) x + D 1 (D 1 _) x + D 2 (D 2 _) x =
    D 0 (D 0 f) (cyc x) + D 1 (D 1 f) (cyc x) + D 2 (D 2 f) (cyc x)
  rw [diag_cyc hf 0, diag_cyc hf 1, diag_cyc hf 2]
  change D 2 (D 2 f) (cyc x) + D 0 (D 0 f) (cyc x) + D 1 (D 1 f) (cyc x) = _
  ring

private theorem psi_cyc : (fun y => psi (cyc y)) = psi := by
  funext x
  have hq : normSq3 (cyc x) = normSq3 x := by
    change x 1 * x 1 + x 2 * x 2 + x 0 * x 0 = x 0 * x 0 + x 1 * x 1 + x 2 * x 2
    ring
  simp only [psi, hq]

private theorem scalarHeat_cyc (n : ℕ) :
    (fun y => scalarHeat n psi (cyc y)) = scalarHeat n psi := by
  induction n with
  | zero => exact psi_cyc
  | succ n ih =>
    change (fun y => L (scalarHeat n psi) (cyc y)) = L (scalarHeat n psi)
    rw [← lap_cyc (scalarHeat_analytic psi_analytic n), ih]

/-- Exact factor 2/3, derived for the given physical field from the cyclic
permutation of the three spatial coordinates. -/
theorem heat_origin_two_thirds_scalar (n : ℕ) :
    heatIterate n 0 0 = (2 / 3 : ℝ) * scalarHeat (n + 1) psi 0 := by
  let f := scalarHeat n psi
  have hsym : (fun y => f (cyc y)) = f := scalarHeat_cyc n
  have hh (i : Fin 3) : D i (D i f) 0 = D (cycPrev i) (D (cycPrev i) f) 0 := by
    have he := congrFun (diag_cyc (scalarHeat_analytic psi_analytic n) i) (0 : RSpace)
    change D i (D i (fun y => f (cyc y))) 0 =
      D (cycPrev i) (D (cycPrev i) f) (cyc 0) at he
    simpa only [hsym, map_zero] using he
  have h0 : D 0 (D 0 f) 0 = D 2 (D 2 f) 0 := hh 0
  have h1 : D 1 (D 1 f) 0 = D 0 (D 0 f) 0 := hh 1
  rw [congrFun (heat_first_as_transverse_hessian n) (0 : RSpace)]
  change D 1 (D 1 f) 0 + D 2 (D 2 f) 0 =
    (2 / 3 : ℝ) * (D 0 (D 0 f) 0 + D 1 (D 1 f) 0 + D 2 (D 2 f) 0)
  linarith

/-- Sole scalar Taylor extraction obligation after transporting the actual
vector profile and its spatial derivatives. -/
def ScalarRadialHeatExtraction : Prop :=
  ∀ n : ℕ, scalarHeat (n + 1) psi 0 = CondPoly.radialDeltaIter (n + 1) CondPoly.radialCoeff 0

theorem radial_heat_of_scalar_extraction (h : ScalarRadialHeatExtraction) (n : ℕ) :
    heatIterate n 0 0 = CondPoly.radialJet n := by
  simpa only [CondPoly.radialJet, h n] using heat_origin_two_thirds_scalar n

end
end CondFeffA
