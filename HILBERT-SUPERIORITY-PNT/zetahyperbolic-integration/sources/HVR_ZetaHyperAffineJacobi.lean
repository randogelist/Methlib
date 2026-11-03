import Mathlib

/-!
Generic finite real affine Jacobi material extracted from the audited
zetahyperbolic-axiom source at b56c8102d25b931a601992c93bf30b19cc7ee103,
src/LeanPaper/ImportedSection3/Jacobi.lean. The unrelated manuscript-specific
imports and final manuscript-specialization theorem are omitted. This port
requires a fresh external Lean 4.34.0-rc1 build and named axiom audits.
-/

noncomputable section
open Matrix Polynomial
namespace PaperAdvances.Theorem3_8_Jacobi

/-- The polynomial determinant for the identity-centered pencil. -/
def unitDetPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ[X]) +
    (Polynomial.X : ℝ[X]) • A.map Polynomial.C)

/-- General finite-dimensional Jacobi coefficient at the identity matrix. -/
theorem unitDetPoly_derivative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Polynomial.derivative (unitDetPoly A)).eval 0 = A.trace := by
  -- This is Mathlib's exact all-dimensions Jacobi derivative at the identity.
  -- The explicit polynomial coefficient ring in `unitDetPoly` resolves `Semiring ?m`.
  exact Matrix.derivative_det_one_add_X_smul A

/-- The polynomial determinant evaluates to the real matrix determinant. -/
theorem unitDetPoly_eval {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (unitDetPoly A).eval t = (1 + t • A).det := by
  let P : Matrix (Fin n) (Fin n) ℝ[X] :=
    (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
      (Polynomial.X : ℝ[X]) • A.map Polynomial.C
  have hmat : P.map (Polynomial.evalRingHom t) = 1 + t • A := by
    classical
    ext i j
    -- Separate diagonal/off-diagonal entries so evaluation of the identity
    -- matrix entry reduces definitionally to 1 or 0. Ring normalisation then
    -- closes the remaining scalar commutativity (a * t = t * a).
    by_cases hij : i = j
    · subst j
      simp [P, Matrix.one_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] <;> ring
    · simp [P, Matrix.one_apply, hij, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] <;> ring
  have hdet : (Polynomial.evalRingHom t) P.det =
      (P.map (Polynomial.evalRingHom t)).det := by
    exact RingHom.map_det (Polynomial.evalRingHom t) P
  calc
    (unitDetPoly A).eval t = (Polynomial.evalRingHom t) P.det := by rfl
    _ = (P.map (Polynomial.evalRingHom t)).det := hdet
    _ = (1 + t • A).det := congrArg Matrix.det hmat

/-- Identity-centered determinant differentiation in every dimension. -/
theorem unitDet_hasDerivAt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  have hp := (unitDetPoly A).hasDerivAt (0 : ℝ)
  have hcoeff :
      (Polynomial.derivative (unitDetPoly A)).eval (0 : ℝ) = A.trace :=
    unitDetPoly_derivative A
  rw [hcoeff] at hp
  have heq : (fun t : ℝ => (1 + t • A).det) =
      (fun t : ℝ => (unitDetPoly A).eval t) := by
    funext t
    exact (unitDetPoly_eval A t).symm
  rw [heq]
  exact hp

/-- Any nonsingular affine matrix pencil factors over real matrices. -/
theorem affineDet_factor_pointwise {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.det ≠ 0) (t : ℝ) :
    (G + t • H).det = G.det * (1 + t • (G⁻¹ * H)).det := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hinv : G * (G⁻¹ * H) = H := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu, Matrix.one_mul]
  have hfac : G * (1 + t • (G⁻¹ * H)) = G + t • H := by
    calc
      G * (1 + t • (G⁻¹ * H)) = G + t • (G * (G⁻¹ * H)) := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      _ = G + t • H := by rw [hinv]
  rw [← hfac, Matrix.det_mul]

/-- Jacobi's determinant derivative at the affine pencil center. -/
theorem affineDet_hasDerivAt {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (G + t • H).det)
      (G.det * (G⁻¹ * H).trace) 0 := by
  have heq : (fun t : ℝ => (G + t • H).det) =
      (fun t : ℝ => G.det * (1 + t • (G⁻¹ * H)).det) := by
    funext t
    exact affineDet_factor_pointwise G H hG t
  rw [heq]
  exact (unitDet_hasDerivAt (G⁻¹ * H)).const_mul G.det

/-- Jacobi's logarithmic determinant derivative at the affine pencil center. -/
theorem affineDet_log_hasDerivAt {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℝ)
    (hG : 0 < G.det) :
    HasDerivAt (fun t : ℝ => Real.log ((G + t • H).det))
      (G⁻¹ * H).trace 0 := by
  have hn : (G + (0 : ℝ) • H).det ≠ 0 := by
    simpa using (ne_of_gt hG)
  have hh := (affineDet_hasDerivAt G H (ne_of_gt hG)).log hn
  have hdiv : G.det * (G⁻¹ * H).trace /
      (G + (0 : ℝ) • H).det = (G⁻¹ * H).trace := by
    simp only [zero_smul, add_zero]
    field_simp [ne_of_gt hG]
  rw [hdiv] at hh
  exact hh


end PaperAdvances.Theorem3_8_Jacobi

