import SingularClosure.CriticalPhysicalH1

/-! Rough periodic transport skew-symmetry from genuine H1 closure and weak
incompressibility.  The smooth approximants need not be solenoidal. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace SingularClosure

noncomputable section

theorem critical_L2_inner_integrable (v w : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube)) :
    IntegrableOn (fun x => inner ℝ (v x) (w x)) unitCube volume := by
  have hi := hv.norm.integrable_mul (q := 2) hw.norm
  apply hi.mono' (hv.aestronglyMeasurable.inner hw.aestronglyMeasurable)
  exact Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) (v x) (w x)

def criticalCoordinateTest (v u : Field) (j : Fin 3) : Field :=
  fun x => v x j • u x

theorem criticalCoordinateTest_memLp (v u : Field) (j : Fin 3)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hu : Continuous u) :
    MemLp (criticalCoordinateTest v u j) 2 (volume.restrict unitCube) := by
  have hvj : MemLp (fun x => v x j) 2 (volume.restrict unitCube) :=
    (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).comp_memLp' hv
  exact MemLp.smul (p := 2) (q := ∞) (critical_continuous_memLp_cube u hu ∞) hvj

theorem critical_matrix_apply_eq_sum (G : Vec →L[ℝ] Vec) (v : Vec) :
    G v = ∑ j : Fin 3, v j • G (unitVector j) := by
  have h := congrArg G (sum_coordinate_unitVector v)
  simpa only [map_sum, map_smul] using h.symm

/-- The actual rough advective pairing; `G` is the physical weak derivative. -/
def criticalRoughTransport (v : Field) (G : Vec → (Vec →L[ℝ] Vec)) (u : Field) : ℝ :=
  ∫ x in unitCube, inner ℝ (u x) (G x (v x))

theorem criticalRoughTransport_eq_sum (v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (u : Field) (hv : MemLp v 2 (volume.restrict unitCube))
    (hG : MemLp G 2 (volume.restrict unitCube)) (hu : Continuous u) :
    criticalRoughTransport v G u =
      ∑ j : Fin 3, physicalFieldInner (fun x => G x (unitVector j))
        (criticalCoordinateTest v u j) := by
  have hpoint (x : Vec) : inner ℝ (u x) (G x (v x)) =
      ∑ j : Fin 3, inner ℝ (G x (unitVector j)) (criticalCoordinateTest v u j x) := by
    rw [critical_matrix_apply_eq_sum, inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [criticalCoordinateTest, inner_smul_right]
    rw [real_inner_comm (u x) (G x (unitVector j))]
  unfold criticalRoughTransport
  simp_rw [hpoint]
  apply integral_finsetSum Finset.univ
  intro j _
  exact critical_L2_inner_integrable _ _
    ((ContinuousLinearMap.apply ℝ Vec (unitVector j)).comp_memLp' hG)
    (criticalCoordinateTest_memLp v u j hv hu)

theorem criticalWeakTransport_eq_sum (v u : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) (hu : ContDiff ℝ ∞ u) :
    criticalWeakTransport v u =
      ∑ j : Fin 3, physicalFieldInner v
        (criticalCoordinateTest v (coordinateDerivative u j) j) := by
  have hpoint (x : Vec) : inner ℝ (v x) ((fderiv ℝ u x) (v x)) =
      ∑ j : Fin 3, inner ℝ (v x)
        (criticalCoordinateTest v (coordinateDerivative u j) j x) := by
    rw [critical_matrix_apply_eq_sum, inner_sum]
    rfl
  unfold criticalWeakTransport
  simp_rw [hpoint]
  apply integral_finsetSum Finset.univ
  intro j _
  exact critical_L2_inner_integrable _ _ hv
    (criticalCoordinateTest_memLp v (coordinateDerivative u j) j hv
      (coordinateDerivative_continuous hu j))

/-- Weak incompressibility is tested only against smooth scalar functions.
H1 approximation then proves the actual rough transport skew identity. -/
theorem CRITICAL_ROUGH_TRANSPORT_SKEW
    (v : Field) (G : Vec → (Vec →L[ℝ] Vec)) (u : Field)
    (hv : CriticalPhysicalH1 v G)
    (hdiv : ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner v (gradient f) = 0)
    (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u) :
    criticalWeakTransport v u = -criticalRoughTransport v G u := by
  obtain ⟨w, hw, hwp, hvel, hderiv⟩ := hv.approximation
  have hwL2 (n : ℕ) : MemLp (w n) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (hw n).continuous 2
  have hwDL2 (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ ((hw n).continuous_fderiv (by simp)) 2
  let A : Fin 3 → Field := fun j => criticalCoordinateTest v u j
  let B : Fin 3 → Field := fun j => criticalCoordinateTest v (coordinateDerivative u j) j
  have hA (j : Fin 3) : MemLp (A j) 2 (volume.restrict unitCube) :=
    criticalCoordinateTest_memLp v u j hv.velocity_L2 hu.continuous
  have hB (j : Fin 3) : MemLp (B j) 2 (volume.restrict unitCube) :=
    criticalCoordinateTest_memLp v (coordinateDerivative u j) j hv.velocity_L2
      (coordinateDerivative_continuous hu j)
  have hzero (n : ℕ) :
      (∑ j : Fin 3, (physicalFieldInner (coordinateDerivative (w n) j) (A j) +
        physicalFieldInner (w n) (B j))) = 0 := by
    let f : Vec → ℝ := fun x => inner ℝ (u x) (w n x)
    have hf : ContDiff ℝ ∞ f := hu.inner ℝ (hw n)
    have hfp : SpatialPeriodic f := by
      intro x i
      change inner ℝ (u (x + unitVector i)) (w n (x + unitVector i)) = _
      rw [hup, hwp n]
    have hd (j : Fin 3) (x : Vec) : fderiv ℝ f x (unitVector j) =
        inner ℝ (u x) (coordinateDerivative (w n) j x) +
          inner ℝ (coordinateDerivative u j x) (w n x) := by
      have h := (((hu.differentiable (by simp)) x).hasFDerivAt).inner ℝ
        (((hw n).differentiable (by simp) x).hasFDerivAt)
      change fderiv ℝ (fun y => inner ℝ (u y) (w n y)) x (unitVector j) = _
      rw [h.fderiv]
      simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
        ContinuousLinearMap.prod_apply, coordinateDerivative]
    have hpoint (x : Vec) : inner ℝ (v x) (gradient f x) =
        ∑ j : Fin 3, (inner ℝ (coordinateDerivative (w n) j x) (A j x) +
          inner ℝ (w n x) (B j x)) := by
      have hinner (a b : Vec) : inner ℝ a b = ∑ j : Fin 3, a j * b j := by
        simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      rw [hinner]
      change (∑ j : Fin 3, v x j * fderiv ℝ f x (unitVector j)) = _
      apply Finset.sum_congr rfl
      intro j _
      rw [hd]
      simp only [A, B, criticalCoordinateTest, inner_smul_right]
      rw [real_inner_comm (coordinateDerivative (w n) j x) (u x),
        real_inner_comm (w n x) (coordinateDerivative u j x)]
      ring
    have hintA (j : Fin 3) : IntegrableOn
        (fun x => inner ℝ (coordinateDerivative (w n) j x) (A j x)) unitCube volume :=
      critical_L2_inner_integrable _ _
        (critical_continuous_memLp_cube _ (coordinateDerivative_continuous (hw n) j) 2) (hA j)
    have hintB (j : Fin 3) : IntegrableOn
        (fun x => inner ℝ (w n x) (B j x)) unitCube volume :=
      critical_L2_inner_integrable _ _ (hwL2 n) (hB j)
    have hsplit (j : Fin 3) :
        (∫ x in unitCube, inner ℝ (coordinateDerivative (w n) j x) (A j x) +
          inner ℝ (w n x) (B j x)) =
        physicalFieldInner (coordinateDerivative (w n) j) (A j) +
          physicalFieldInner (w n) (B j) :=
      integral_add (hintA j) (hintB j)
    have hz := hdiv f hf hfp
    unfold physicalFieldInner at hz
    simp_rw [hpoint] at hz
    have hsumIntegral :
        (∫ x in unitCube, ∑ j : Fin 3,
          (inner ℝ (coordinateDerivative (w n) j x) (A j x) +
            inner ℝ (w n x) (B j x))) =
        ∑ j : Fin 3, (∫ x in unitCube,
          inner ℝ (coordinateDerivative (w n) j x) (A j x) +
            inner ℝ (w n x) (B j x)) := by
      apply integral_finsetSum Finset.univ
      intro j _
      exact (hintA j).add (hintB j)
    rw [hsumIntegral] at hz
    simp_rw [hsplit] at hz
    exact hz
  have hlimit : Tendsto (fun n =>
      ∑ j : Fin 3, (physicalFieldInner (coordinateDerivative (w n) j) (A j) +
        physicalFieldInner (w n) (B j))) atTop
      (𝓝 (∑ j : Fin 3, (physicalFieldInner (fun x => G x (unitVector j)) (A j) +
        physicalFieldInner v (B j)))) := by
    apply tendsto_finsetSum Finset.univ
    intro j _
    have ha : Tendsto (fun n => physicalFieldInner (coordinateDerivative (w n) j) (A j))
        atTop (𝓝 (physicalFieldInner (fun x => G x (unitVector j)) (A j))) := by
      change Tendsto (fun n => physicalFieldInner
        (fun x => fderiv ℝ (w n) x (unitVector j)) (A j)) atTop
        (𝓝 (physicalFieldInner (fun x => G x (unitVector j)) (A j)))
      simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
        critical_physicalFieldInner_compCLM_tendsto
          (ContinuousLinearMap.apply ℝ Vec (unitVector j))
          (fun n => fderiv ℝ (w n)) G (A j) hwDL2 hv.derivative_L2 (hA j) hderiv
    exact ha.add (critical_physicalFieldInner_tendsto w v (B j)
      hwL2 hv.velocity_L2 (hB j) hvel)
  have hsum : (∑ j : Fin 3, (physicalFieldInner (fun x => G x (unitVector j)) (A j) +
      physicalFieldInner v (B j))) = 0 := by
    apply tendsto_nhds_unique hlimit
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [Finset.sum_add_distrib] at hsum
  change (∑ j : Fin 3, physicalFieldInner (fun x => G x (unitVector j))
      (criticalCoordinateTest v u j)) +
    (∑ j : Fin 3, physicalFieldInner v
      (criticalCoordinateTest v (coordinateDerivative u j) j)) = 0 at hsum
  rw [← criticalRoughTransport_eq_sum v G u hv.velocity_L2 hv.derivative_L2 hu.continuous,
    ← criticalWeakTransport_eq_sum v u hv.velocity_L2 hu] at hsum
  linarith

end

end SingularClosure
