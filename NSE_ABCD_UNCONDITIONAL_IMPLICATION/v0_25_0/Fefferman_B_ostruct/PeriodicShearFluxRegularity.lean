import PeriodicShearFlux
import PeriodicShearHeat

noncomputable section
open Fefferman Fefferman.ConcreteReal Set
open scoped BigOperators

namespace CondFeffB

/-- A spatial slice of `smoothClosedHalfSpaceReal` has all the package's spatial regularity,
    including a slice at the initial time. -/
theorem contDiff_spatialSlice {F : RSpace → ℝ → ℝ} (hF : smoothClosedHalfSpaceReal F)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ⊤ (fun x => F x t) := by
  change ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => F z.1 z.2) {z | 0 ≤ z.2} at hF
  exact hF.comp_contDiff (contDiff_prodMk_left t) (fun _ => ht)

theorem shearVelocity_slice_two {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (i : Fin 3) :
    ContDiff ℝ 2 (fun x : RSpace => shearVelocity ν x t i) := by
  by_cases hi : i = 0
  · simp only [shearVelocity, if_pos hi]
    exact (shearProfile_contDiff_two hν ht).comp (contDiff_apply ℝ ℝ (1 : Fin 3))
  · simp only [shearVelocity, if_neg hi]
    exact contDiff_const

theorem spatialDerivative_contDiff_one {f : RSpace → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    ContDiff ℝ 1 (spatialDerivative j f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem differenceFlux_contDiff_one (ν : ℝ) (U W : RSpace → RVector) (P : RSpace → ℝ)
    (hU : ∀ j, ContDiff ℝ 1 (fun x => U x j)) (hW : ∀ i, ContDiff ℝ 2 (fun x => W x i))
    (hP : ContDiff ℝ 1 P) (j : Fin 3) : ContDiff ℝ 1 (fun x => differenceFlux ν U W P x j) := by
  have hW₁ (i : Fin 3) : ContDiff ℝ 1 (fun x => W x i) := (hW i).of_le (by norm_num)
  have hA : ContDiff ℝ 1 (fun x => ∑ i, W x i * spatialDerivative j (fun y => W y i) x) :=
    ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun (i : Fin 3) (x : RSpace) => W x i * spatialDerivative j (fun y => W y i) x)
      (fun i _ => (hW₁ i).mul (spatialDerivative_contDiff_one (hW i) j))
  have hB : ContDiff ℝ 1 (fun x => ∑ i, (W x i)^2) :=
    ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun (i : Fin 3) (x : RSpace) => (W x i)^2) (fun i _ => (hW₁ i).pow 2)
  exact (((contDiff_const (c := 2 * ν)).mul hA).sub ((hU j).mul hB)).sub
    (((contDiff_const (c := (2 : ℝ))).mul hP).mul (hW₁ j))

private theorem unitShift_as_add (x : RSpace) (j : Fin 3) :
    unitShift realAnalysis x j = x + basisDirection j := by
  funext i
  by_cases h : i = j <;> simp [unitShift, realAnalysis, basisDirection, h]

theorem spatialDerivative_periodic {f : RSpace → ℝ}
    (h : ∀ x k, f (unitShift realAnalysis x k) = f x) (x : RSpace) (j k : Fin 3) :
    spatialDerivative j f (unitShift realAnalysis x k) = spatialDerivative j f x := by
  have he : (fun z : RSpace => f (z + basisDirection k)) = f := by
    funext z
    simpa only [unitShift_as_add] using h z k
  unfold spatialDerivative
  rw [unitShift_as_add, ← fderiv_comp_add_right (basisDirection k), he]

theorem differenceFlux_periodic (ν : ℝ) (U W : RSpace → RVector) (P : RSpace → ℝ)
    (hU : ∀ x k, U (unitShift realAnalysis x k) = U x)
    (hW : ∀ x k, W (unitShift realAnalysis x k) = W x)
    (hP : ∀ x k, P (unitShift realAnalysis x k) = P x) (x : RSpace) (j k : Fin 3) :
    differenceFlux ν U W P (unitShift realAnalysis x k) j = differenceFlux ν U W P x j := by
  have hD (i : Fin 3) := spatialDerivative_periodic (f := fun z => W z i)
    (fun z k => congrFun (hW z k) i) x j k
  simp only [differenceFlux, hD, hU, hW, hP]

abbrev candidateDifference (s : Solution realAnalysis) (ν t : ℝ) : RSpace → RVector :=
  fun x i => s.velocity x t i - shearVelocity ν x t i

abbrev candidateFlux (s : Solution realAnalysis) (ν t : ℝ) : RSpace → RVector :=
  differenceFlux ν (fun x => s.velocity x t) (candidateDifference s ν t) (fun x => s.pressure x t)

theorem candidateFlux_regular {s : Solution realAnalysis} {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {f : RForce} (hs : globalSolution realAnalysis .periodic ν a f s)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) : ContDiff ℝ 1 (fun x => candidateFlux s ν.val t x j) := by
  have hreg : clause06 realAnalysis s := hs.2.2.2.2.1
  have hU (i : Fin 3) : ContDiff ℝ ⊤ (fun x => s.velocity x t i) :=
    contDiff_spatialSlice (F := fun (x : RSpace) (r : ℝ) => s.velocity x r i)
      (t := t) (hreg.1 i) ht
  have hν : 0 ≤ ν.val := le_of_lt ν.property
  apply differenceFlux_contDiff_one ν.val (fun x => s.velocity x t)
    (candidateDifference s ν.val t) (fun x => s.pressure x t)
  · exact fun i => (hU i).of_le le_top
  · exact fun i => ((hU i).of_le le_top).sub (shearVelocity_slice_two hν ht i)
  · exact (contDiff_spatialSlice (F := fun (x : RSpace) (r : ℝ) => s.pressure x r)
      (t := t) hreg.2 ht).of_le le_top

theorem candidateFlux_periodic {s : Solution realAnalysis} {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {f : RForce} (hs : globalSolution realAnalysis .periodic ν a f s)
    {t : ℝ} (ht : 0 ≤ t) (x : RSpace) (j k : Fin 3) :
    candidateFlux s ν.val t (unitShift realAnalysis x k) j = candidateFlux s ν.val t x j := by
  have hU : vectorPeriodic realAnalysis s.velocity := hs.2.2.2.1
  have hP : pressurePeriodic realAnalysis s.pressure := hs.2.2.2.2.2
  apply differenceFlux_periodic
  · exact fun z k => hU z t ht k
  · intro z k
    funext i
    change s.velocity (unitShift realAnalysis z k) t i - shearVelocity ν.val (unitShift realAnalysis z k) t i = _
    rw [hU z t ht k, shearVelocity_periodic ν.val z t ht k]
  · exact fun z k => hP z t ht k

/-- The four differentiability hypotheses consumed by the product rule for the spatial flux. -/
theorem candidateSlice_differentiable {s : Solution realAnalysis} {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {f : RForce} (hs : globalSolution realAnalysis .periodic ν a f s)
    {t : ℝ} (ht : 0 ≤ t) (x : RSpace) :
    (∀ i, DifferentiableAt ℝ (fun y => s.velocity y t i) x) ∧
    (∀ i, DifferentiableAt ℝ (fun y => candidateDifference s ν.val t y i) x) ∧
    (∀ j i, DifferentiableAt ℝ (spatialDerivative j (fun y => candidateDifference s ν.val t y i)) x) ∧
    DifferentiableAt ℝ (fun y => s.pressure y t) x := by
  have hreg : clause06 realAnalysis s := hs.2.2.2.2.1
  have hU (i : Fin 3) : ContDiff ℝ ⊤ (fun y => s.velocity y t i) :=
    contDiff_spatialSlice (F := fun (y : RSpace) (r : ℝ) => s.velocity y r i)
      (t := t) (hreg.1 i) ht
  have hν : 0 ≤ ν.val := le_of_lt ν.property
  have hW (i : Fin 3) : ContDiff ℝ 2 (fun y => candidateDifference s ν.val t y i) :=
    ((hU i).of_le le_top).sub (shearVelocity_slice_two hν ht i)
  exact ⟨fun i => (hU i).differentiable (by simp) x,
    fun i => (hW i).differentiable (by norm_num) x,
    fun j i => (spatialDerivative_contDiff_one
      (f := fun y => candidateDifference s ν.val t y i) (hW i) j).differentiable one_ne_zero x,
    (contDiff_spatialSlice (F := fun (y : RSpace) (r : ℝ) => s.pressure y r)
      (t := t) hreg.2 ht).differentiable (by simp) x⟩

end CondFeffB
