import SingularClosure.CoordinateAverage

/-!
# Differentiation of the actual coordinate average

The derivative interchange is proved from the pinned dominated differentiation
theorem. The domination follows from compactness of a physical neighbourhood
times the integration interval; it is not an additional admission premise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Metric Filter
open scoped BigOperators ContDiff Topology

namespace SingularClosure

noncomputable section

def coordinateResetLinear (j : Fin 3) : Vec →L[ℝ] Vec :=
  ContinuousLinearMap.id ℝ Vec - (EuclideanSpace.proj j).smulRight (unitVector j)

theorem resetCoordinate_eq_linear (j : Fin 3) (s : ℝ) (x : Vec) :
    resetCoordinate j s x = coordinateResetLinear j x + s • unitVector j := by
  ext i
  by_cases h : i = j
  · subst i
    simp [coordinateResetLinear, unitVector]
  · simp [coordinateResetLinear, unitVector, h]

theorem coordinateResetLinear_other (i j : Fin 3) (hij : i ≠ j) :
    coordinateResetLinear j (unitVector i) = unitVector i := by
  simp [coordinateResetLinear, unitVector, Ne.symm hij]

theorem coordinateAverage_integrand_hasFDerivAt (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (s : ℝ) (x : Vec) :
    HasFDerivAt (fun y : Vec => a (resetCoordinate j s y))
      ((fderiv ℝ a (resetCoordinate j s x)).comp (coordinateResetLinear j)) x := by
  have h := ((ha.differentiable (by simp))
    (coordinateResetLinear j x + s • unitVector j)).hasFDerivAt.comp x
      ((coordinateResetLinear j).hasFDerivAt.add_const (s • unitVector j))
  simpa only [resetCoordinate_eq_linear] using h

theorem coordinateAverage_integrand_derivative_continuous (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) :
    Continuous (fun z : Vec × ℝ =>
      (fderiv ℝ a (resetCoordinate j z.2 z.1)).comp (coordinateResetLinear j)) := by
  exact ((ha.continuous_fderiv (by simp)).comp
    (resetCoordinate_smooth j).continuous).clm_comp continuous_const

theorem coordinateAverage_integrand_derivative_integrable (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (x : Vec) :
    IntegrableOn (fun s : ℝ =>
      (fderiv ℝ a (resetCoordinate j s x)).comp (coordinateResetLinear j))
      (Icc (0 : ℝ) 1) volume := by
  have h := (coordinateAverage_integrand_derivative_continuous j a ha).comp
    (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => (x, s)))
  exact h.continuousOn.integrableOn_compact isCompact_Icc

theorem coordinateAverage_hasFDerivAt (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (x : Vec) :
    HasFDerivAt (coordinateAverage j a)
      (∫ s in Icc (0 : ℝ) 1,
        (fderiv ℝ a (resetCoordinate j s x)).comp (coordinateResetLinear j)) x := by
  let D : Vec × ℝ → Vec →L[ℝ] Vec := fun z =>
    (fderiv ℝ a (resetCoordinate j z.2 z.1)).comp (coordinateResetLinear j)
  have hD : Continuous D := coordinateAverage_integrand_derivative_continuous j a ha
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).bddAbove_image hD.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y s => a (resetCoordinate j s y))
    (F' := fun y s => D (y, s))
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (bound := fun _ => M)
    (s := closedBall x 1)
  · exact closedBall_mem_nhds x (by norm_num)
  · filter_upwards with y
    exact (ha.continuous.comp (resetCoordinate_continuous_slice j y)).aestronglyMeasurable
  · exact coordinateAverage_slice_integrable j a ha.continuous x
  · exact (hD.comp
      (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => (x, s)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs y hy
    exact hM (mem_image_of_mem _ ⟨hy, hs⟩)
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards with s y hy
    exact coordinateAverage_integrand_hasFDerivAt j a ha s y

theorem coordinateAverage_fderiv_apply (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (x v : Vec) :
    fderiv ℝ (coordinateAverage j a) x v =
      coordinateAverage j (fun y => fderiv ℝ a y (coordinateResetLinear j v)) x := by
  rw [(coordinateAverage_hasFDerivAt j a ha x).fderiv]
  rw [ContinuousLinearMap.integral_apply
    (coordinateAverage_integrand_derivative_integrable j a ha x)]
  rfl

/-- The actual coordinate average preserves every finite differentiability order. -/
theorem coordinateAverage_smooth (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (coordinateAverage j a) := by
  have hn : ∀ (n : ℕ) (b : Field), ContDiff ℝ ∞ b →
      ContDiff ℝ n (coordinateAverage j b) := by
    intro n
    induction n with
    | zero =>
        intro b hb
        simpa using coordinateAverage_continuous j b hb.continuous
    | succ n ih =>
        intro b hb
        rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv_apply]
        refine ⟨fun x => (coordinateAverage_hasFDerivAt j b hb x).differentiableAt,
          by simp, ?_⟩
        intro v
        have hv : ContDiff ℝ ∞
            (fun y => fderiv ℝ b y (coordinateResetLinear j v)) :=
          (contDiff_infty_iff_fderiv.mp hb).2.clm_apply contDiff_const
        have he : (fun x => fderiv ℝ (coordinateAverage j b) x v) =
            coordinateAverage j (fun y => fderiv ℝ b y (coordinateResetLinear j v)) := by
          funext x
          exact coordinateAverage_fderiv_apply j b hb x v
        rw [he]
        exact ih _ hv
  exact contDiff_infty.mpr (fun n => hn n a ha)

/-- Cross-coordinate differentiation commutes with literal physical averaging. -/
theorem coordinateAverage_coordinateDerivative_commute
    (i j : Fin 3) (hij : i ≠ j) (a : Field) (ha : ContDiff ℝ ∞ a) :
    coordinateDerivative (coordinateAverage j a) i =
      coordinateAverage j (coordinateDerivative a i) := by
  funext x
  unfold coordinateDerivative
  rw [(coordinateAverage_hasFDerivAt j a ha x).fderiv]
  rw [ContinuousLinearMap.integral_apply
    (coordinateAverage_integrand_derivative_integrable j a ha x)]
  simp only [ContinuousLinearMap.comp_apply, coordinateResetLinear_other i j hij,
    coordinateAverage, coordinateDerivative]

/-- A periodic full-coordinate derivative has zero average by the interval FTC. -/
theorem coordinateAverage_own_derivative_eq_zero (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateAverage j (coordinateDerivative a j) = 0 := by
  funext x
  have hderiv (s : ℝ) :
      HasDerivAt (fun t : ℝ => a (resetCoordinate j t x))
        (coordinateDerivative a j (resetCoordinate j s x)) s := by
    have hl : HasDerivAt (fun t : ℝ => coordinateResetLinear j x + t • unitVector j)
        (unitVector j) s := by
      simpa using ((hasDerivAt_id s).smul_const (unitVector j)).const_add
        (coordinateResetLinear j x)
    have hc := ((ha.differentiable (by simp)) (resetCoordinate j s x)).hasFDerivAt
      .comp_hasDerivAt_of_eq s hl (resetCoordinate_eq_linear j s x)
    simpa only [Function.comp_def, resetCoordinate_eq_linear, coordinateDerivative] using hc
  have hcont : Continuous (fun s : ℝ => coordinateDerivative a j (resetCoordinate j s x)) := by
    exact ((ha.continuous_fderiv (by simp)).comp
      (resetCoordinate_continuous_slice j x)).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun s _ => hderiv s) (hcont.intervalIntegrable 0 1)
  change (∫ s in Icc (0 : ℝ) 1,
    coordinateDerivative a j (resetCoordinate j s x)) = 0
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hFTC]
  have hend : a (resetCoordinate j 1 x) = a (resetCoordinate j 0 x) := by
    simpa only [resetCoordinate_eq_linear, zero_smul, add_zero, one_smul] using
      hp (coordinateResetLinear j x) j
  rw [hend, sub_self]

/-- Every physical coordinate derivative commutes with averaging on smooth periodic fields. -/
theorem coordinateAverage_all_coordinateDerivative_commute
    (i j : Fin 3) (a : Field) (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateDerivative (coordinateAverage j a) i =
      coordinateAverage j (coordinateDerivative a i) := by
  by_cases hij : i = j
  · subst i
    rw [coordinateAverage_own_derivative_eq_zero j a ha hp]
    funext x
    exact coordinateAverage_own_coordinateDerivative_zero j a x
  · exact coordinateAverage_coordinateDerivative_commute i j hij a ha

theorem coordinateAverage_component (j : Fin 3) (a : Field)
    (ha : Continuous a) (x : Vec) (i : Fin 3) :
    coordinateAverage j a x i =
      ∫ s in Icc (0 : ℝ) 1, a (resetCoordinate j s x) i :=
  ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).integral_comp_comm
    (coordinateAverage_slice_integrable j a ha x)).symm

/-- Literal divergence freedom is preserved by the physical average. -/
theorem coordinateAverage_divergence_free (j : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (x : Vec) :
    divergence (coordinateAverage j a) x = 0 := by
  have hc (i : Fin 3) : Continuous (coordinateDerivative a i) :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi (i : Fin 3) : IntegrableOn
      (fun s : ℝ => coordinateDerivative a i (resetCoordinate j s x) i)
      (Icc (0 : ℝ) 1) volume := by
    exact ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      ((hc i).comp (resetCoordinate_continuous_slice j x))).continuousOn.integrableOn_compact
        isCompact_Icc
  have hcomm (i : Fin 3) := coordinateAverage_all_coordinateDerivative_commute i j a ha hp
  have hcomponent (i : Fin 3) :=
    coordinateAverage_component j (coordinateDerivative a i) (hc i) x i
  unfold divergence
  simp_rw [hcomm, hcomponent]
  rw [← integral_finset_sum Finset.univ (fun i _ => hi i)]
  change (∫ s in Icc (0 : ℝ) 1, divergence a (resetCoordinate j s x)) = 0
  simp only [hd, integral_zero]

end

end SingularClosure
