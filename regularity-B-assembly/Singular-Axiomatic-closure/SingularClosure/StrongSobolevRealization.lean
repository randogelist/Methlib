import SingularClosure.UniformStrongBounds
import SingularClosure.TorusGalerkinSobolev

/-! Frozen endpoint 7 in the actual weighted Fourier Hilbert spaces. -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.sobolevState_H1_square_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖g.sobolevState 1 t‖ ^ 2 = physicalH1Square (g.velocity t) := by
  rw [g.sobolevState_H1_physical_norm_sq ht, physicalH1Square,
    physicalEnergy_eq_integral_norm_sq, physicalDissipation]

theorem GalerkinSolution.sobolevState_H2_square_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖g.sobolevState 2 t‖ ^ 2 = physicalH2Square (g.velocity t) := by
  rw [g.sobolevState_H2_physical_norm_sq ht, physicalH2Square,
    physicalEnergy_eq_integral_norm_sq, physicalDissipation]

theorem AX6_UNIFORM_STRONG_BOUNDS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState 1 t‖ ^ 2 ≤ B) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ B ∧
      IntervalIntegrable (fun t => ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) ≤ B := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_PHYSICAL_STRONG_BOUNDS hAX6 ν hν a ha T hT
  refine ⟨B, hB, ?_⟩
  intro N hN g
  obtain ⟨h1, hi2, h2, hit, ht⟩ := hb N hN g
  have hi : IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T := by
    apply hi2.congr
    intro t ht
    have hm : t ∈ Ioc (0 : ℝ) T := by simpa only [uIoc_of_le hT.le] using ht
    exact (g.sobolevState_H2_square_eq hm.1.le).symm
  have he : (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) =
      ∫ t in (0 : ℝ)..T, physicalH2Square (g.velocity t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hm : t ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le hT.le] using ht
    exact g.sobolevState_H2_square_eq hm.1
  refine ⟨?_, hi, he.trans_le h2, hit, ht⟩
  intro t ht
  rw [g.sobolevState_H1_square_eq ht.1]
  exact h1 t ht

end

end SingularClosure
