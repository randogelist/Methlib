import SingularClosure.SmoothSixOrthogonal
import SingularClosure.PhysicalParseval

/-!
# Six-channel enstrophy for arbitrary smooth periodic physical fields

The projections are the literal coordinate-average operators.  There is no
Fourier cutoff, finite-support premise, or assumed orthogonality argument in
the endpoint type.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem integral_unitCube_norm_sum_sq_of_orthogonal (v : Fin 6 → Field)
    (hv : ∀ A, Continuous (v A))
    (horth : ∀ A B, A ≠ B →
      (∫ x in unitCube, inner ℝ (v A x) (v B x)) = 0) :
    (∫ x in unitCube, ‖∑ A : Fin 6, v A x‖ ^ 2) =
      ∑ A : Fin 6, ∫ x in unitCube, ‖v A x‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [integral_finsetSum Finset.univ
    (f := fun A x => ∑ B : Fin 6, inner ℝ (v A x) (v B x))
    (μ := volume.restrict unitCube) (fun A _ =>
    (continuous_finsetSum Finset.univ (fun B _ =>
      (hv A).inner (hv B))).continuousOn.integrableOn_compact isCompact_unitCube)]
  apply Finset.sum_congr rfl
  intro A _
  rw [integral_finsetSum Finset.univ
    (f := fun B x => inner ℝ (v A x) (v B x))
    (μ := volume.restrict unitCube) (fun B _ =>
    ((hv A).inner (hv B)).continuousOn.integrableOn_compact isCompact_unitCube)]
  rw [Finset.sum_eq_single A]
  · intro B _ hBA
    exact horth A B hBA.symm
  · intro hA
    exact (hA (Finset.mem_univ A)).elim

theorem coordinateDerivative_smooth {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (coordinateDerivative a i) :=
  (contDiff_infty_iff_fderiv.mp ha).2.clm_apply contDiff_const

theorem integral_coordinateDerivative_norm_sq_smooth_channels
    (a : Field) (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    (∫ x in unitCube, ‖coordinateDerivative a i x‖ ^ 2) =
      ∑ A : Fin 6, ∫ x in unitCube,
        ‖coordinateDerivative (smoothSixChannel A a) i x‖ ^ 2 := by
  have had := coordinateDerivative_smooth ha i
  have h := integral_unitCube_norm_sum_sq_of_orthogonal
    (fun A => smoothSixChannel A (coordinateDerivative a i))
    (fun A => (smoothSixChannel_smooth A _ had).continuous)
    (fun A B hAB => smoothSixChannel_orthogonal A B hAB _ _ had had)
  have hrec (x : Vec) :
      (∑ A : Fin 6, smoothSixChannel A (coordinateDerivative a i) x) =
        coordinateDerivative a i x := by
    have hr := congrArg (fun b : Field => b x)
      (SMOOTH_SIX_CHANNEL_RECONSTRUCTION (coordinateDerivative a i))
    simpa using hr
  have hcomm (A : Fin 6) := smoothSixChannel_coordinateDerivative A i a ha hp
  simp_rw [hrec, ← hcomm] at h
  exact h

theorem integral_gradientSquareDensity_norm {a : Field} (ha : ContDiff ℝ ∞ a) :
    (∫ x in unitCube, gradientSquareDensity a x) =
      ∑ i : Fin 3, ∫ x in unitCube, ‖coordinateDerivative a i x‖ ^ 2 := by
  have hpoint (x : Vec) : gradientSquareDensity a x =
      ∑ i : Fin 3, ‖coordinateDerivative a i x‖ ^ 2 := by
    simp only [gradientSquareDensity, EuclideanSpace.real_norm_sq_eq]
  simp_rw [hpoint]
  exact integral_finsetSum Finset.univ (fun i _ =>
    ((coordinateDerivative_continuous ha i).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube)

theorem SIX_CHANNEL_REAL_ENSTROPHY_EQ (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    (∫ x in unitCube, gradientSquareDensity a x) =
      ∑ A : Fin 6, ∫ x in unitCube,
        gradientSquareDensity (smoothSixChannel A a) x := by
  calc
    _ = ∑ i : Fin 3, ∫ x in unitCube, ‖coordinateDerivative a i x‖ ^ 2 :=
      integral_gradientSquareDensity_norm ha
    _ = ∑ i : Fin 3, ∑ A : Fin 6, ∫ x in unitCube,
        ‖coordinateDerivative (smoothSixChannel A a) i x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_coordinateDerivative_norm_sq_smooth_channels a ha hp i
    _ = ∑ A : Fin 6, ∑ i : Fin 3, ∫ x in unitCube,
        ‖coordinateDerivative (smoothSixChannel A a) i x‖ ^ 2 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      exact (integral_gradientSquareDensity_norm (smoothSixChannel_smooth A a ha)).symm

/-- Frozen endpoint 2 on the complete class of smooth periodic physical fields.
No solenoidality, mean-zero, smallness, finite-frequency, or analytic admission
premise is required for the orthogonal gradient identity. -/
theorem SIX_CHANNEL_ENSTROPHY_EQ (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    (∑ A : Fin 6, physicalEnstrophy (smoothSixChannel A a)) = physicalEnstrophy a := by
  rw [physicalEnstrophy_eq_ofReal_integral ha, SIX_CHANNEL_REAL_ENSTROPHY_EQ a ha hp,
    ENNReal.ofReal_sum_of_nonneg (fun A _ =>
      integral_nonneg (gradientSquareDensity_nonneg (smoothSixChannel A a)))]
  apply Finset.sum_congr rfl
  intro A _
  exact physicalEnstrophy_eq_ofReal_integral (smoothSixChannel_smooth A a ha)

end

end SingularClosure
