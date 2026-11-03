import HVR_ZetaHyperAffineJacobi

/-!
Generic matrix-curve Jacobi identity adapted from the audited
zetahyperbolic-axiom source at b56c8102d25b931a601992c93bf30b19cc7ee103,
src/LeanPaper/MatrixCurveJacobi.lean. Import redirected to the extracted
standalone affine result. Fresh external RC1 compilation and audit required.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix Polynomial

namespace ManuscriptChain.MatrixCurveJacobi


def directionalDet {n : ℕ} (G H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, G (σ j) j) * H (σ i) i

theorem curve_det_leibniz {n : ℕ}
    {F : ℝ → Matrix (Fin n) (Fin n) ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    {τ : ℝ} (hF : ∀ i j, HasDerivAt (fun z => F z i j) (H i j) τ) :
    HasDerivAt (fun z => (F z).det) (directionalDet (F τ) H) τ := by
  classical
  have hσ (σ : Equiv.Perm (Fin n)) :
      HasDerivAt (fun z => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i : Fin n, F z (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, F τ (σ j) j) * H (σ i) i) τ := by
    have hp := HasDerivAt.fun_finsetProd
      (u := (Finset.univ : Finset (Fin n))) (fun i _ => hF (σ i) i)
    simpa only [smul_eq_mul] using hp.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))
  simpa only [Matrix.det_apply', directionalDet] using
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (fun σ _ => hσ σ)

theorem directionalDet_eq_trace {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) :
    directionalDet G H = G.det * (G⁻¹ * H).trace := by
  have hentry (i j : Fin n) :
      HasDerivAt (fun z : ℝ => (G + z • H) i j) (H i j) 0 := by
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, id] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (H i j)).const_add (G i j)
  have h := curve_det_leibniz hentry
  simp only [zero_smul, add_zero] at h
  exact h.unique (PaperAdvances.Theorem3_8_Jacobi.affineDet_hasDerivAt G H hG)

theorem generic_det_hasDerivAt {n : ℕ}
    {F : ℝ → Matrix (Fin n) (Fin n) ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    {τ : ℝ} (hF : ∀ i j, HasDerivAt (fun z => F z i j) (H i j) τ)
    (hdet : (F τ).det ≠ 0) :
    HasDerivAt (fun z => (F z).det) ((F τ).det * ((F τ)⁻¹ * H).trace) τ := by
  rw [← directionalDet_eq_trace (F τ) H hdet]
  exact curve_det_leibniz hF

theorem generic_logDet_hasDerivAt {n : ℕ}
    {F : ℝ → Matrix (Fin n) (Fin n) ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    {τ : ℝ} (hF : ∀ i j, HasDerivAt (fun z => F z i j) (H i j) τ)
    (hdet : (F τ).det ≠ 0) :
    HasDerivAt (fun z => Real.log ((F z).det)) (((F τ)⁻¹ * H).trace) τ := by
  have h := (generic_det_hasDerivAt hF hdet).log hdet
  have he : (F τ).det * ((F τ)⁻¹ * H).trace / (F τ).det =
      ((F τ)⁻¹ * H).trace := by field_simp
  rwa [he] at h


end ManuscriptChain.MatrixCurveJacobi


