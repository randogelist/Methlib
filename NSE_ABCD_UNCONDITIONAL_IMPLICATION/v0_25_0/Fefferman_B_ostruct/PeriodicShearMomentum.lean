import PeriodicShearHeat

noncomputable section
open Fefferman Fefferman.ConcreteReal Set
open scoped BigOperators Topology ContDiff

namespace CondFeffB

def relativeVelocity (u : RVelocity) (ν : ℝ) : RVelocity :=
  fun x t i => u x t i - shearVelocity ν x t i

def dxV (u : RVelocity) (j i : Fin 3) (t : ℝ) (x : RSpace) : ℝ :=
  spatialDerivative j (fun y => u y t i) x

def dxxV (u : RVelocity) (j i : Fin 3) (t : ℝ) (x : RSpace) : ℝ :=
  spatialDerivative j (dxV u j i t) x

private theorem smoothSpatialSlice {f : RSpace → ℝ → ℝ}
    (hf : smoothClosedHalfSpaceReal f) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (fun x => f x t) := by
  apply contDiffOn_univ.mp
  exact (show ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => f z.1 z.2)
    {z | 0 ≤ z.2} from hf).comp (contDiff_prodMk_left t).contDiffOn (fun _ _ => ht)

private theorem differentiableTimeSlice {f : RSpace → ℝ → ℝ}
    (hf : smoothClosedHalfSpaceReal f) (x : RSpace) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (f x) t := by
  have h : ContDiffOn ℝ ⊤ (f x) (Ici 0) :=
    (show ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => f z.1 z.2) {z | 0 ≤ z.2} from hf).comp
      (contDiff_prodMk_right x).contDiffOn (fun _ hs => hs)
  exact (h.contDiffAt (Ici_mem_nhds ht)).differentiableAt (by simp)

theorem candidate_velocity_spatial_slice {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) : ContDiff ℝ ⊤ (fun x => s.velocity x t i) :=
  smoothSpatialSlice (f := fun (y : RSpace) (r : ℝ) => s.velocity y r i)
    (hs.2.2.2.2.1.1 i) ht

theorem candidate_pressure_spatial_slice {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ⊤ (fun x => s.pressure x t) :=
  smoothSpatialSlice (f := s.pressure) hs.2.2.2.2.1.2 ht

private theorem coord_differentiable {f : ℝ → ℝ} {b : ℝ} {x : RSpace}
    (hf : HasDerivAt f b (x 1)) :
    DifferentiableAt ℝ (fun y : RSpace => f (y 1)) x :=
  (hf.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x)).differentiableAt

private theorem coord_dx {f : ℝ → ℝ} {b : ℝ} (j : Fin 3) (x : RSpace)
    (hf : HasDerivAt f b (x 1)) :
    spatialDerivative j (fun y : RSpace => f (y 1)) x = if j = 1 then b else 0 := by
  change (fderiv ℝ (f ∘ fun y : RSpace => y 1) x) (basisDirection j) = _
  rw [(hf.comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x)).fderiv]
  change b * (if (1 : Fin 3) = j then 1 else 0) = (if j = 1 then b else 0)
  by_cases hj : j = 1
  · subst j; simp
  · simp [hj, Ne.symm hj]

theorem dxV_shear {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (j i : Fin 3) (x : RSpace) :
    dxV (shearVelocity ν) j i t x =
      if i = 0 ∧ j = 1 then shearSlope ν t (x 1) else 0 := by
  by_cases hi : i = 0
  · subst i
    simpa [dxV, shearVelocity] using coord_dx j x
      (shearProfile_hasDerivAt_space hν ht (x 1))
  · simp [dxV, shearVelocity, hi, spatialDerivative]

theorem dxxV_shear {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (j i : Fin 3) (x : RSpace) :
    dxxV (shearVelocity ν) j i t x =
      if i = 0 ∧ j = 1 then shearCurvature ν t (x 1) else 0 := by
  have hfun : dxV (shearVelocity ν) j i t =
    fun y => if i = 0 ∧ j = 1 then shearSlope ν t (y 1) else 0 :=
    funext (dxV_shear hν ht j i)
  unfold dxxV
  rw [hfun]
  by_cases h : i = 0 ∧ j = 1
  · rcases h with ⟨rfl, rfl⟩
    simpa using coord_dx 1 x (shearSlope_hasDerivAt_space hν ht (x 1))
  · simp [h, spatialDerivative]

private theorem shear_space_diff {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (i : Fin 3) :
    Differentiable ℝ (fun x => shearVelocity ν x t i) := by
  intro x
  by_cases hi : i = 0
  · simpa [shearVelocity, hi] using
      coord_differentiable (x := x) (shearProfile_hasDerivAt_space hν ht (x 1))
  · simp [shearVelocity, hi, differentiableAt_const]

private theorem shear_dx_diff {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (j i : Fin 3) :
    Differentiable ℝ (dxV (shearVelocity ν) j i t) := by
  have hfun : dxV (shearVelocity ν) j i t =
    fun y => if i = 0 ∧ j = 1 then shearSlope ν t (y 1) else 0 := funext (dxV_shear hν ht j i)
  rw [hfun]
  by_cases h : i = 0 ∧ j = 1
  · simp only [if_pos h]
    exact fun x => coord_differentiable (shearSlope_hasDerivAt_space hν ht (x 1))
  · simp [h, differentiable_const]

private theorem shear_time_derivative {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (i : Fin 3) (x : RSpace) :
    HasDerivAt (fun r => shearVelocity ν x r i)
      (if i = 0 then ν * shearCurvature ν t (x 1) else 0) t := by
  by_cases hi : i = 0
  · simpa [shearVelocity, hi] using shearProfile_hasDerivAt_time hν ht (x 1)
  · simpa [shearVelocity, hi] using (hasDerivAt_const t (0 : ℝ))

private theorem dx_sub {f g : RSpace → ℝ} (j : Fin 3) (x : RSpace)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spatialDerivative j (fun y => f y - g y) x =
    spatialDerivative j f x - spatialDerivative j g x := by
  simp only [spatialDerivative, fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

theorem dxV_relative {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) (j i : Fin 3) (x : RSpace) :
    dxV (relativeVelocity s.velocity ν.val) j i t x =
      dxV s.velocity j i t x - dxV (shearVelocity ν.val) j i t x :=
  dx_sub j x ((candidate_velocity_spatial_slice hs ht i).differentiable (by simp) x)
    (shear_space_diff (le_of_lt ν.property) ht i x)

theorem dxxV_relative {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) (j i : Fin 3) (x : RSpace) :
    dxxV (relativeVelocity s.velocity ν.val) j i t x =
      dxxV s.velocity j i t x - dxxV (shearVelocity ν.val) j i t x := by
  have hup : ContDiff ℝ 1 (dxV s.velocity j i t) :=
    ((candidate_velocity_spatial_slice hs ht i).fderiv_right
      (m := (1 : ℕ∞ω)) le_top).clm_apply contDiff_const
  have hfun : dxV (relativeVelocity s.velocity ν.val) j i t =
    fun y => dxV s.velocity j i t y - dxV (shearVelocity ν.val) j i t y :=
    funext (dxV_relative hs ht j i)
  rw [dxxV, hfun]
  exact dx_sub j x (hup.differentiable (by simp) x)
    (shear_dx_diff (le_of_lt ν.property) ht j i x)

theorem candidate_divergence {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) (x : RSpace) : ∑ j, dxV s.velocity j j t x = 0 := by
  rw [Fin.sum_univ_three]
  exact hs.2.1 x t ht

theorem relative_divergence {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 ≤ t) (x : RSpace) :
    ∑ j, dxV (relativeVelocity s.velocity ν.val) j j t x = 0 := by
  have hj (j : Fin 3) : dxV (shearVelocity ν.val) j j t x = 0 := by
    rw [dxV_shear (le_of_lt ν.property) ht]
    exact if_neg (fun h => (by decide : (0 : Fin 3) ≠ 1) (h.1.symm.trans h.2))
  simpa only [dxV_relative hs ht, hj, sub_zero] using (candidate_divergence hs ht x)

theorem deriv_relative {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) (x : RSpace) (i : Fin 3) :
    deriv (fun r => relativeVelocity s.velocity ν.val x r i) t =
      deriv (fun r => s.velocity x r i) t - deriv (fun r => shearVelocity ν.val x r i) t :=
  deriv_fun_sub (differentiableTimeSlice
    (f := fun (y : RSpace) (r : ℝ) => s.velocity y r i) (hs.2.2.2.2.1.1 i) x ht)
    (shear_time_derivative (le_of_lt ν.property) ht i x).differentiableAt

theorem relative_momentum {ν : PositiveViscosity realAnalysis} {a : RInitial}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) (x : RSpace) (i : Fin 3) :
    deriv (fun r => relativeVelocity s.velocity ν.val x r i) t +
        (∑ j, s.velocity x t j * dxV (relativeVelocity s.velocity ν.val) j i t x) +
        (if i = 0 then relativeVelocity s.velocity ν.val x t 1 * shearSlope ν.val t (x 1) else 0)
      = ν.val * (∑ j, dxxV (relativeVelocity s.velocity ν.val) j i t x) -
        spatialDerivative i (fun y => s.pressure y t) x := by
  have hν : 0 ≤ ν.val := le_of_lt ν.property
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := h01.symm
  have hu : deriv (fun r => s.velocity x r i) t + (∑ j, s.velocity x t j * dxV s.velocity j i t x)
      = ν.val * (∑ j, dxxV s.velocity j i t x) - spatialDerivative i (fun y => s.pressure y t) x := by
    have hconv : sum3 realAnalysis (fun j => s.velocity x t j * dxV s.velocity j i t x) =
        ∑ j, s.velocity x t j * dxV s.velocity j i t x := by
      rw [Fin.sum_univ_three] <;> rfl
    have hlap : laplacian realAnalysis (fun y => s.velocity y t i) x =
        ∑ j, dxxV s.velocity j i t x := by
      rw [Fin.sum_univ_three] <;> rfl
    have hp := hs.1 x t ht.le i
    change deriv (fun r => s.velocity x r i) t +
        sum3 realAnalysis (fun j => s.velocity x t j * dxV s.velocity j i t x) =
      (ν.val * laplacian realAnalysis (fun y => s.velocity y t i) x +
        (-spatialDerivative i (fun y => s.pressure y t) x)) + 0 at hp
    rw [hconv, hlap, add_zero, ← sub_eq_add_neg] at hp
    exact hp
  have hv := shear_time_derivative hν ht i x
  have he : deriv (fun r => shearVelocity ν.val x r i) t =
      ν.val * (∑ j, dxxV (shearVelocity ν.val) j i t x) := by
    rw [hv.deriv]
    by_cases hi : i = 0 <;> simp [Fin.sum_univ_three, dxxV_shear hν ht.le, hi, h01, h21]
  have htransport :
      (∑ j, s.velocity x t j * dxV (relativeVelocity s.velocity ν.val) j i t x) +
        (if i = 0 then relativeVelocity s.velocity ν.val x t 1 * shearSlope ν.val t (x 1) else 0)
      = ∑ j, s.velocity x t j * dxV s.velocity j i t x := by
    simp only [Fin.sum_univ_three, dxV_relative hs ht.le, dxV_shear hν ht.le]
    by_cases hi : i = 0 <;> simp [hi, h01, h21, h10, relativeVelocity, shearVelocity] <;> ring
  have hdiff : (∑ j, dxxV (relativeVelocity s.velocity ν.val) j i t x) =
      (∑ j, dxxV s.velocity j i t x) - (∑ j, dxxV (shearVelocity ν.val) j i t x) := by
    simp only [dxxV_relative hs ht.le, Finset.sum_sub_distrib]
  rw [deriv_relative hs ht x i, add_assoc, htransport, hdiff]
  linear_combination hu - he

#print axioms relative_momentum
#print axioms relative_divergence

end CondFeffB
