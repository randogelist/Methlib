import SingularClosure.UniformStrongBounds
import SingularClosure.TorusGalerkinSobolev
import SingularClosure.SobolevTrajectoryCalculus

/-! Frozen endpoint 7 in the actual weighted Fourier Hilbert spaces. -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval ENNReal

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

theorem AX6_UNIFORM_SOBOLEV_NORM_BOUNDS (hAX6 : AX6Statement)
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

/-- Frozen endpoint 7 with actual Bochner membership and the identified Hilbert-space
time derivative, in addition to the cutoff-independent physical bounds. -/
theorem AX6_UNIFORM_STRONG_BOUNDS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ContinuousOn (g.sobolevState 1) (Ici 0) ∧
      MemLp (g.sobolevState 1) ⊤ (volume.restrict (Icc (0 : ℝ) T)) ∧
      MemLp (g.sobolevState 2) 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      MemLp (g.rhsSobolev 0) 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (g.sobolevState 0)
        (g.rhsSobolev 0 t) (Ici 0) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState 1 t‖ ^ 2 ≤ B) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ B ∧
      IntervalIntegrable (fun t => ‖g.rhsSobolev 0 t‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ‖g.rhsSobolev 0 t‖ ^ 2) ≤ B ∧
      IntervalIntegrable (fun t => ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) ≤ B := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_SOBOLEV_NORM_BOUNDS hAX6 ν hν a ha T hT
  refine ⟨B, hB, ?_⟩
  intro N hN g
  obtain ⟨h1, hi2, h2, hid, hd⟩ := hb N hN g
  have hi : IntervalIntegrable (fun t => ‖g.rhsSobolev 0 t‖ ^ 2) volume 0 T := by
    apply hid.congr
    intro t ht
    have hm : t ∈ Ioc (0 : ℝ) T := by simpa only [uIoc_of_le hT.le] using ht
    exact (g.rhsSobolev_H0_physical_norm_sq t hm.1.le).symm
  have he : (∫ t in (0 : ℝ)..T, ‖g.rhsSobolev 0 t‖ ^ 2) =
      ∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hm : t ∈ Icc (0 : ℝ) T := by simpa only [uIcc_of_le hT.le] using ht
    exact g.rhsSobolev_H0_physical_norm_sq t hm.1
  refine ⟨g.sobolevState_continuousOn 1, g.sobolevState_memLp 1 T ⊤,
    g.sobolevState_memLp 2 T 2, g.rhsSobolev_memLp 0 T 2, ?_,
    h1, hi2, h2, hi, he.trans_le hd, hid, hd⟩
  intro t ht
  exact g.sobolevState_hasDerivWithinAt 0 t ht

end

end SingularClosure
