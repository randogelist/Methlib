import Mathlib

/-!
Euclidean coefficient magnitude for the exact caloric estimates.
The default norm on Fin 3 → ℂ is deliberately not used.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuasiFeffermanB
noncomputable section

/-- Hermitian Euclidean coefficient magnitude, explicitly a square sum. -/
def complexVecNorm (c : Fin 3 → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ‖c i‖ ^ 2)

/-- Finite Fourier ℓ¹ norm of the Euclidean coefficient magnitudes. -/
def finiteChi0 {ι : Type*} (s : Finset ι) (c : ι → Fin 3 → ℂ) : ℝ :=
  ∑ k ∈ s, complexVecNorm (c k)

theorem complexVecNorm_nonneg (c : Fin 3 → ℂ) : 0 ≤ complexVecNorm c :=
  Real.sqrt_nonneg _

theorem complexVecNorm_sq (c : Fin 3 → ℂ) :
    complexVecNorm c ^ 2 = ∑ i : Fin 3, ‖c i‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖c i‖)

theorem norm_component_le_complexVecNorm (c : Fin 3 → ℂ) (i : Fin 3) :
    ‖c i‖ ≤ complexVecNorm c := by
  have hsq : ‖c i‖ ^ 2 ≤ ∑ j : Fin 3, ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) (Finset.mem_univ i)
  rw [← complexVecNorm_sq] at hsq
  nlinarith [norm_nonneg (c i), complexVecNorm_nonneg c]

theorem finiteChi0_nonneg {ι : Type*} (s : Finset ι) (c : ι → Fin 3 → ℂ) :
    0 ≤ finiteChi0 s c := by
  exact Finset.sum_nonneg fun k _ => complexVecNorm_nonneg (c k)

/-- The real two-coordinate Cauchy inequality underlying the sharp symmetric
Leray multiplier, before any Fourier or time integration. -/
theorem SYMMETRIC_SPLIT_SCALAR_SQUARE
    (a b x y : ℝ) :
    (a * y + b * x) ^ 2 ≤ (a ^ 2 + x ^ 2) * (b ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (a * b - x * y)]


/-- Explicit isometric interpretation of a coefficient as a complex Euclidean
vector. This transports norm estimates without using the Pi sup norm. -/
def complexVec (c : Fin 3 → ℂ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 c

theorem complexVecNorm_eq_norm (c : Fin 3 → ℂ) :
    complexVecNorm c = ‖complexVec c‖ := by
  exact (EuclideanSpace.norm_eq (complexVec c)).symm

theorem complexVecNorm_add_le (c d : Fin 3 → ℂ) :
    complexVecNorm (fun i => c i + d i) ≤ complexVecNorm c + complexVecNorm d := by
  rw [complexVecNorm_eq_norm, complexVecNorm_eq_norm, complexVecNorm_eq_norm]
  change ‖complexVec c + complexVec d‖ ≤ ‖complexVec c‖ + ‖complexVec d‖
  exact norm_add _ _

theorem complexVecNorm_smul (α : ℂ) (c : Fin 3 → ℂ) :
    complexVecNorm (fun i => α * c i) = ‖α‖ * complexVecNorm c := by
  rw [complexVecNorm_eq_norm, complexVecNorm_eq_norm]
  change ‖α • complexVec c‖ = ‖α‖ * ‖complexVec c‖
  exact norm_smul α (complexVec c)

/-- Orthogonal transverse part for a unit normal; used only with an explicit
unit-normal hypothesis in the sharp estimate below. -/
def complexTransverse (e z : EuclideanSpace ℂ (Fin 3)) :
    EuclideanSpace ℂ (Fin 3) :=
  z - (inner ℂ e z) • e

theorem complexTransverse_symmetric
    (e z w : EuclideanSpace ℂ (Fin 3)) :
    complexTransverse e ((inner ℂ e z) • w + (inner ℂ e w) • z) =
      (inner ℂ e z) • complexTransverse e w +
        (inner ℂ e w) • complexTransverse e z := by
  simp only [complexTransverse, inner_add_right, inner_smul_right,
    smul_sub, add_smul, mul_smul]
  abel

theorem complexTransverse_pythagoras
    (e z : EuclideanSpace ℂ (Fin 3)) (he : ‖e‖ = 1) :
    ‖z‖ ^ 2 = ‖inner ℂ e z‖ ^ 2 + ‖complexTransverse e z‖ ^ 2 := by
  have hee : inner ℂ e e = 1 := inner_self_eq_one_of_norm_eq_one he
  have horth :
      inner ℂ ((inner ℂ e z) • e) (complexTransverse e z) = 0 := by
    simp only [complexTransverse, inner_smul_left, inner_sub_right,
      inner_smul_right, hee, mul_one, sub_self, mul_zero]
  have hdecomp :
      (inner ℂ e z) • e + complexTransverse e z = z := by
    simp only [complexTransverse]
    abel
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((inner ℂ e z) • e) (complexTransverse e z) horth
  simpa only [hdecomp, norm_smul, he, mul_one, pow_two] using hp

/-- Sharp symmetric complex Leray multiplier, in the Hermitian Euclidean norm.
The unit normal may be complex; real Fourier unit normals are a special case. -/
theorem SYMMETRIC_COMPLEX_LERAY_MULTIPLIER
    (e z w : EuclideanSpace ℂ (Fin 3)) (he : ‖e‖ = 1) :
    ‖complexTransverse e ((inner ℂ e z) • w + (inner ℂ e w) • z)‖ ≤
      ‖z‖ * ‖w‖ := by
  have hz := complexTransverse_pythagoras e z he
  have hw := complexTransverse_pythagoras e w he
  have hcs := SYMMETRIC_SPLIT_SCALAR_SQUARE
    ‖inner ℂ e z‖ ‖inner ℂ e w‖ ‖complexTransverse e z‖ ‖complexTransverse e w‖
  have hsq :
      (‖inner ℂ e z‖ * ‖complexTransverse e w‖ +
        ‖inner ℂ e w‖ * ‖complexTransverse e z‖) ^ 2 ≤
      (‖z‖ * ‖w‖) ^ 2 := by
    rw [← hz, ← hw] at hcs
    simpa only [mul_pow] using hcs
  have hscalar :
      ‖inner ℂ e z‖ * ‖complexTransverse e w‖ +
        ‖inner ℂ e w‖ * ‖complexTransverse e z‖ ≤ ‖z‖ * ‖w‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  rw [complexTransverse_symmetric]
  exact (norm_add_le _ _).trans (by simpa only [norm_smul] using hscalar)

/-- Multiplication by the Fourier derivative and symmetrization gives κ/2. -/
theorem SYMMETRIC_COMPLEX_LERAY_MULTIPLIER_SCALED
    (κ : ℝ) (hκ : 0 ≤ κ)
    (e z w : EuclideanSpace ℂ (Fin 3)) (he : ‖e‖ = 1) :
    ‖((κ / 2 : ℝ) : ℂ) •
      complexTransverse e ((inner ℂ e z) • w + (inner ℂ e w) • z)‖ ≤
      (κ / 2) * (‖z‖ * ‖w‖) := by
  have hnorm : ‖((κ / 2 : ℝ) : ℂ)‖ = κ / 2 := by
    simp [abs_of_nonneg (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 2))]
  rw [norm_smul, hnorm]
  exact mul_le_mul_of_nonneg_left
    (SYMMETRIC_COMPLEX_LERAY_MULTIPLIER e z w he)
    (div_nonneg hκ (by norm_num))

end
end QuasiFeffermanB

