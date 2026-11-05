import ConcreteABCDUnifiedClosure

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal

noncomputable section

local notation "D" => spatialDerivative

/-- Coordinate 0 of the package is the first physical coordinate. -/
def psi (x : RSpace) : ℝ :=
  Real.exp (-(normSq3 x)) / (1 + normSq3 x)

def profile (x : RSpace) (i : Fin 3) : ℝ :=
  (if i = 0 then laplacian realAnalysis psi x else 0) - D i (D 0 psi) x

def datum (c : ℝ) : RInitial := fun x i => c * profile x i

def unitViscosity : PositiveViscosity realAnalysis :=
  ⟨(1 : ℝ), by change (0 : ℝ) < 1; norm_num⟩

theorem psi_denom_pos (x : RSpace) : 0 < 1 + normSq3 x := by
  unfold normSq3
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem psi_analytic : ContDiff ℝ ⊤ psi := by
  have hq : ContDiff ℝ ⊤ normSq3 := by
    unfold normSq3
    fun_prop
  exact hq.neg.exp.div (contDiff_const.add hq)
    (fun x => ne_of_gt (psi_denom_pos x))

theorem partial_analytic {f : RSpace → ℝ}
    (hf : ContDiff ℝ ⊤ f) (i : Fin 3) : ContDiff ℝ ⊤ (D i f) := by
  have hdf : ContDiff ℝ ⊤ (fderiv ℝ f) := hf.fderiv_right le_top
  exact (contDiff_clm_apply_iff.mp hdf) (basisDirection i)

private theorem partial_partial {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f)
    (i j : Fin 3) (x : RSpace) :
    D i (D j f) x =
      (fderiv ℝ (fderiv ℝ f) x) (basisDirection i) (basisDirection j) := by
  have hdf : ContDiff ℝ ⊤ (fderiv ℝ f) := hf.fderiv_right le_top
  unfold spatialDerivative
  rw [fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : RSpace => basisDirection j)
    (hdf.differentiable (by simp) x) (by fun_prop)]
  simp

theorem partial_comm {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f)
    (i j : Fin 3) (x : RSpace) : D i (D j f) x = D j (D i f) x := by
  rw [partial_partial hf, partial_partial hf]
  exact (hf.contDiffAt (x := x)).isSymmSndFDerivAt_of_omega
    (basisDirection i) (basisDirection j)

theorem partial_add {f g : RSpace → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (i : Fin 3) (x : RSpace) :
    D i (fun y => f y + g y) x = D i f x + D i g x := by
  simp only [spatialDerivative, fderiv_fun_add (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x), ContinuousLinearMap.add_apply]

private theorem partial_neg (f : RSpace → ℝ) (i : Fin 3) (x : RSpace) :
    D i (fun y => -f y) x = -D i f x := by
  simp [spatialDerivative, fderiv_fun_neg]

private theorem partial_const_mul {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f)
    (c : ℝ) (i : Fin 3) (x : RSpace) :
    D i (fun y => c * f y) x = c * D i f x := by
  simp [spatialDerivative, fderiv_const_mul (hf.differentiable (by simp) x) c]

theorem profile_first :
    (fun x => profile x 0) = fun x => D 1 (D 1 psi) x + D 2 (D 2 psi) x := by
  funext x
  change (D 0 (D 0 psi) x + D 1 (D 1 psi) x + D 2 (D 2 psi) x)
    - D 0 (D 0 psi) x = _
  ring

private theorem profile_other (j : Fin 3) (hj : j ≠ 0) :
    (fun x => profile x j) = fun x => -D 0 (D j psi) x := by
  funext x
  simp only [profile, if_neg hj, zero_sub]
  rw [partial_comm psi_analytic j 0]

theorem profile_analytic (i : Fin 3) : ContDiff ℝ ⊤ (fun x => profile x i) := by
  by_cases hi : i = 0
  · subst i
    rw [profile_first]
    exact (partial_analytic (partial_analytic psi_analytic 1) 1).add
      (partial_analytic (partial_analytic psi_analytic 2) 2)
  · rw [profile_other i hi]
    exact (partial_analytic (partial_analytic psi_analytic i) 0).neg

theorem datum_initialSmooth (c : ℝ) : initialSmooth realAnalysis (datum c) := by
  intro i
  exact contDiff_const.mul (profile_analytic i)

theorem profile_divergenceFree : initialDivergenceFree realAnalysis profile := by
  intro x
  change D 0 (fun y => profile y 0) x + D 1 (fun y => profile y 1) x +
    D 2 (fun y => profile y 2) x = 0
  rw [profile_first, profile_other 1 (by decide), profile_other 2 (by decide)]
  rw [partial_add (partial_analytic (partial_analytic psi_analytic 1) 1)
      (partial_analytic (partial_analytic psi_analytic 2) 2),
    partial_neg, partial_neg]
  rw [partial_comm (partial_analytic psi_analytic 1) 0 1,
    partial_comm (partial_analytic psi_analytic 2) 0 2]
  ring

theorem datum_divergenceFree (c : ℝ) : initialDivergenceFree realAnalysis (datum c) := by
  intro x
  change D 0 (fun y => c * profile y 0) x + D 1 (fun y => c * profile y 1) x +
    D 2 (fun y => c * profile y 2) x = 0
  rw [partial_const_mul (profile_analytic 0), partial_const_mul (profile_analytic 1),
    partial_const_mul (profile_analytic 2)]
  have h := profile_divergenceFree x
  change D 0 (fun y => profile y 0) x + D 1 (fun y => profile y 1) x +
    D 2 (fun y => profile y 2) x = 0 at h
  linear_combination c * h

theorem datum_admissible_of_decay (c : ℝ) (hdec : clause04 realAnalysis (datum c)) :
    admissibleInitial realAnalysis .wholeSpace (datum c) :=
  ⟨datum_initialSmooth c, datum_divergenceFree c, hdec⟩

end

end CondFeffA
