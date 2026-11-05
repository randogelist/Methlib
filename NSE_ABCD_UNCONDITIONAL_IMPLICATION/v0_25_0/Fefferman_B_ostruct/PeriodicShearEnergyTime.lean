import PeriodicShearHeat
import PeriodicShearUniqueness
import PeriodicCellTime

open Fefferman Fefferman.ConcreteReal Set MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace CondFeffB

def componentTimeDerivative (u : RVelocity) (x : RSpace) (t : ℝ) (i : Fin 3) : ℝ :=
  deriv (fun r => u x r i) t

def PositiveTimeDerivativeContinuous (u : RVelocity) : Prop :=
  ∀ i, ContinuousOn
    (fun z : RSpace × ℝ => componentTimeDerivative u z.1 z.2 i) {z | 0 < z.2}

def ComponentHasTimeDerivative (u : RVelocity) : Prop :=
  ∀ x t, 0 < t → ∀ i, HasDerivAt (fun r => u x r i) (componentTimeDerivative u x t i) t

def energyTimeDensity (u v : RVelocity) (t : ℝ) (x : RSpace) : ℝ :=
  ∑ i : Fin 3, 2 * (u x t i - v x t i) *
    (componentTimeDerivative u x t i - componentTimeDerivative v x t i)

private theorem positiveTime_subset_closedTime :
    {z : RSpace × ℝ | 0 < z.2} ⊆ {z : RSpace × ℝ | 0 ≤ z.2} := by
  intro z hz
  change (0 : ℝ) < z.2 at hz
  change (0 : ℝ) ≤ z.2
  exact hz.le

theorem globalSolution_time_derivative {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s) :
    ComponentHasTimeDerivative s.velocity ∧ PositiveTimeDerivativeContinuous s.velocity := by
  let S : Set (RSpace × ℝ) := {z | 0 < z.2}
  have hS : IsOpen S := isOpen_lt continuous_const continuous_snd
  have hboth (i : Fin 3) := show
      (∀ z ∈ S, HasDerivAt (fun t => s.velocity z.1 t i)
        ((fderiv ℝ (fun p : RSpace × ℝ => s.velocity p.1 p.2 i) z) (0, 1)) z.2) ∧
      ContinuousOn (fun z : RSpace × ℝ =>
        (fderiv ℝ (fun p : RSpace × ℝ => s.velocity p.1 p.2 i) z) (0, 1)) S from by
    let F := fun p : RSpace × ℝ => s.velocity p.1 p.2 i
    have hclosed : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2} :=
      (show vectorSmooth realAnalysis s.velocity from hs.2.2.2.2.1.1) i
    have hopen : ContDiffOn ℝ ⊤ F S := hclosed.mono positiveTime_subset_closedTime
    constructor
    · intro z hz
      have hf : DifferentiableAt ℝ F z :=
        (hopen.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
      have hline : HasDerivAt (fun q : ℝ => (z.1, q)) ((0 : RSpace), (1 : ℝ)) z.2 :=
        ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
      exact hf.hasFDerivAt.comp_hasDerivAt (f := fun q : ℝ => (z.1, q)) z.2 hline
    · exact (hopen.continuousOn_fderiv_of_isOpen hS le_top).clm_apply
        (continuousOn_const (c := ((0 : RSpace), (1 : ℝ))))
  constructor
  · intro x t ht i
    exact ((hboth i).1 (x,t) ht).differentiableAt.hasDerivAt
  · intro i
    change ContinuousOn (fun z : RSpace × ℝ => deriv (fun q => s.velocity z.1 q i) z.2) S
    exact (hboth i).2.congr (fun z hz => ((hboth i).1 z hz).deriv)

theorem shear_time_derivative_regular (ν : ℝ) (hν : 0 ≤ ν) :
    ComponentHasTimeDerivative (shearVelocity ν) ∧
      PositiveTimeDerivativeContinuous (shearVelocity ν) := by
  have hfirst (x : RSpace) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun r => shearVelocity ν x r 0) (ν * shearCurvature ν t (x 1)) t := by
    simpa [shearVelocity] using shearProfile_hasDerivAt_time hν ht (x 1)
  have hother (x : RSpace) (t : ℝ) {i : Fin 3} (hi : i ≠ 0) :
      HasDerivAt (fun r => shearVelocity ν x r i) 0 t := by
    simpa [shearVelocity, hi] using hasDerivAt_const t (0 : ℝ)
  constructor
  · intro x t ht i
    by_cases hi : i = 0
    · subst i; exact (hfirst x t ht).differentiableAt.hasDerivAt
    · exact (hother x t hi).differentiableAt.hasDerivAt
  · intro i
    by_cases hi : i = 0
    · subst i
      have hc : ContinuousOn (fun z : RSpace × ℝ => shearCurvature ν z.2 (z.1 1))
          {z | 0 < z.2} :=
        (shearCurvature_continuousOn ν hν).comp
          (f := fun z : RSpace × ℝ => (z.2,z.1 1))
          (continuous_snd.prodMk ((continuous_apply 1).comp continuous_fst)).continuousOn
          (by
            intro z hz
            change (0 : ℝ) < z.2 at hz
            change (0 : ℝ) ≤ z.2
            exact hz.le)
      have hscaled : ContinuousOn (fun z : RSpace × ℝ => ν * shearCurvature ν z.2 (z.1 1))
          {z | 0 < z.2} := continuousOn_const.mul hc
      change ContinuousOn (fun z : RSpace × ℝ =>
        deriv (fun q => shearVelocity ν z.1 q 0) z.2) {z | 0 < z.2}
      apply hscaled.congr
      intro z hz
      change (0 : ℝ) < z.2 at hz
      exact (hfirst z.1 z.2 hz).deriv
    · change ContinuousOn (fun z : RSpace × ℝ =>
        deriv (fun q => shearVelocity ν z.1 q i) z.2) {z | 0 < z.2}
      exact (continuousOn_const : ContinuousOn (fun _ : RSpace × ℝ => (0 : ℝ))
        {z | 0 < z.2}).congr (fun z _ => (hother z.1 z.2 hi).deriv)

private theorem energyTimeDensity_continuousOn {u v : RVelocity}
    (hu : JointVelocityContinuous u) (hv : JointVelocityContinuous v)
    (hcu : PositiveTimeDerivativeContinuous u) (hcv : PositiveTimeDerivativeContinuous v) :
    ContinuousOn (fun z : RSpace × ℝ => energyTimeDensity u v z.2 z.1) {z | 0 < z.2} := by
  change ContinuousOn (fun z : RSpace × ℝ => ∑ i : Fin 3, 2 * (u z.1 z.2 i - v z.1 z.2 i) *
      (componentTimeDerivative u z.1 z.2 i - componentTimeDerivative v z.1 z.2 i)) {z | 0 < z.2}
  refine continuousOn_finsetSum (f := fun (i : Fin 3) (z : RSpace × ℝ) =>
    2 * (u z.1 z.2 i - v z.1 z.2 i) *
      (componentTimeDerivative u z.1 z.2 i - componentTimeDerivative v z.1 z.2 i))
    (Finset.univ : Finset (Fin 3)) fun i _ => ?_
  have hU := (hu i).mono positiveTime_subset_closedTime
  have hV := (hv i).mono positiveTime_subset_closedTime
  exact ((continuousOn_const (c := (2 : ℝ))).mul (hU.sub hV)).mul ((hcu i).sub (hcv i))

theorem cellEnergy_hasDerivAt {u v : RVelocity}
    (hu : JointVelocityContinuous u) (hv : JointVelocityContinuous v)
    (hdu : ComponentHasTimeDerivative u) (hdv : ComponentHasTimeDerivative v)
    (hcu : PositiveTimeDerivativeContinuous u) (hcv : PositiveTimeDerivativeContinuous v)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cellEnergy u v) (∫ x in centeredCell, energyTimeDensity u v t x) t := by
  refine cellIntegral_hasDerivAt_pos (F := fun z => sqDifference u v z.2 z.1)
    (G := fun z => energyTimeDensity u v z.2 z.1)
    (show IsCompact centeredCell from isCompact_Icc) ?_ ?_ ?_ ht
  · change ContinuousOn (fun z : RSpace × ℝ => ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i)^2)
      (centeredCell ×ˢ Ici (0 : ℝ))
    have hsub : centeredCell ×ˢ Ici (0 : ℝ) ⊆ {z : RSpace × ℝ | 0 ≤ z.2} := by
      intro z hz
      change (0 : ℝ) ≤ z.2
      exact hz.2
    exact continuousOn_finsetSum (f := fun (i : Fin 3) (z : RSpace × ℝ) =>
      (u z.1 z.2 i - v z.1 z.2 i)^2) (Finset.univ : Finset (Fin 3))
      (fun i _ => (((hu i).mono hsub).sub ((hv i).mono hsub)).pow 2)
  · apply (energyTimeDensity_continuousOn hu hv hcu hcv).mono
    intro z hz
    change (0 : ℝ) < z.2
    exact hz.2
  · intro x _ s hs
    change HasDerivAt (fun q : ℝ => ∑ i : Fin 3, (u x q i - v x q i)^2)
      (∑ i : Fin 3, 2 * (u x s i - v x s i) *
        (componentTimeDerivative u x s i - componentTimeDerivative v x s i)) s
    apply HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun i q => (u x q i - v x q i)^2)
      (A' := fun i => 2 * (u x s i - v x s i) *
        (componentTimeDerivative u x s i - componentTimeDerivative v x s i))
    intro i _
    let d : ℝ := componentTimeDerivative u x s i - componentTimeDerivative v x s i
    have hd : HasDerivAt (fun q : ℝ => u x q i - v x q i) d s := by
      with_unfolding_all exact (hdu x s hs i).fun_sub (hdv x s hs i)
    change HasDerivAt (fun q : ℝ => (u x q i - v x q i)^2)
      (2 * (u x s i - v x s i) * d) s
    have hfactor : ((2 : ℕ) : ℝ) * (u x s i - v x s i) ^ (2 - 1 : ℕ) * d =
        2 * (u x s i - v x s i) * d := by norm_num
    with_unfolding_all exact (hd.fun_pow 2).congr_deriv hfactor

theorem candidate_cellEnergy_hasDerivAt {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cellEnergy s.velocity (shearVelocity ν.val))
      (∫ x in centeredCell, energyTimeDensity s.velocity (shearVelocity ν.val) t x) t := by
  have hν : 0 ≤ ν.val := le_of_lt ν.property
  have hU := globalSolution_time_derivative hs
  have hV := shear_time_derivative_regular ν.val hν
  exact cellEnergy_hasDerivAt (jointVelocityContinuous_of_globalSolution hs)
    (shearVelocity_continuousOn ν.val hν) hU.1 hV.1 hU.2 hV.2 ht

theorem candidate_energyTimeDensity_integrableOn {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (energyTimeDensity s.velocity (shearVelocity ν.val) t) centeredCell := by
  have hν : 0 ≤ ν.val := le_of_lt ν.property
  have h := energyTimeDensity_continuousOn (jointVelocityContinuous_of_globalSolution hs)
    (shearVelocity_continuousOn ν.val hν) (globalSolution_time_derivative hs).2
    (shear_time_derivative_regular ν.val hν).2
  have hc : Continuous (energyTimeDensity s.velocity (shearVelocity ν.val) t) :=
    h.comp_continuous (f := fun x : RSpace => (x, t))
      (continuous_id.prodMk continuous_const) (by intro x; change (0 : ℝ) < t; exact ht)
  exact hc.continuousOn.integrableOn_compact (show IsCompact centeredCell from isCompact_Icc)

end CondFeffB
