import SingularClosure.CriticalRegularityContracts
import SingularClosure.PeriodicFourierRealization
import SingularClosure.CriticalSobolevDual
import SingularClosure.PeriodicSobolev

/-! Actual real L2 fields on the physical unit cube.  The torus pullback
uses the proved measure-preserving quotient map and real coordinate maps. -/

set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace SingularClosure
noncomputable section

local instance criticalCubeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance criticalCubeHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance criticalCubeProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev PhysicalCubeL2 := Lp Vec 2 (volume.restrict unitCube)

def criticalCubeTorusMap (x : Vec) : UnitAddTorus (Fin 3) := fun i => (x i : UnitAddCircle)

theorem criticalCubeTorusMap_measurePreserving :
    MeasurePreserving criticalCubeTorusMap (volume.restrict unitCube) volume := by
  let S : Set (Fin 3 → ℝ) := {x | ∀ i : Fin 3, x i ∈ Icc (0 : ℝ) 1}
  have hpre : (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' S = unitCube := by
    ext x
    rfl
  have hof : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume.restrict unitCube) (unitProductMeasure 3) := by
    have h := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage
      (MeasurableSet.univ_pi' (fun _ => measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
    rw [hpre] at h
    change MeasurePreserving _ _
      ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict S) at h
    have hS : S = Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
      ext x
      simp only [S, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    rw [hS, Measure.restrict_pi_pi] at h
    exact h
  have hinterval : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1) = unitIntervalMeasure := by
    exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have hpi : MeasurePreserving
      (fun x : Fin 3 → ℝ => fun i => (x i : UnitAddCircle)) (unitProductMeasure 3)
      (volume : Measure (UnitAddTorus (Fin 3))) := by
    have h := measurePreserving_pi _ _
      (fun _ : Fin 3 => AddCircle.measurePreserving_mk 1 0)
    simp only [zero_add, hinterval] at h
    convert! h using 1 <;> simp [unitProductMeasure, volume, AddCircle.haarAddCircle]
  exact hpi.comp hof

def criticalScalarCubePullback : TorusScalarL2 →L[ℝ] Lp ℂ 2 (volume.restrict unitCube) :=
  (Lp.compMeasurePreservingₗᵢ ℝ criticalCubeTorusMap
    criticalCubeTorusMap_measurePreserving).toContinuousLinearMap

def criticalRealCoordinate (i : Fin 3) : ℂ →L[ℝ] Vec :=
  Complex.reCLM.smulRight (unitVector i)

def torusToPhysicalCubeL2 : TorusVectorL2 →L[ℝ] PhysicalCubeL2 :=
  ∑ i : Fin 3,
    ((criticalRealCoordinate i).compLpL 2 (volume.restrict unitCube)).comp
      (criticalScalarCubePullback.comp
        ((PiLp.proj 2 (fun _ : Fin 3 => TorusScalarL2) (𝕜 := ℂ) i).restrictScalars ℝ))

def physicalFieldL2 (v : Field) (hv : Continuous v) : PhysicalCubeL2 :=
  (critical_continuous_memLp_cube v hv 2).toLp v

theorem physicalFieldL2_coe (v : Field) (hv : Continuous v) :
    physicalFieldL2 v hv =ᵐ[volume.restrict unitCube] v :=
  (critical_continuous_memLp_cube v hv 2).coeFn_toLp

theorem physicalFieldL2_norm_sq (v : Field) (hv : Continuous v) :
    ‖physicalFieldL2 v hv‖ ^ 2 = physicalEnergy v := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [physicalFieldL2_coe v hv] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem physicalFieldL2_sub (v w : Field) (hv : Continuous v) (hw : Continuous w) :
    physicalFieldL2 (v - w) (hv.sub hw) = physicalFieldL2 v hv - physicalFieldL2 w hw := by
  exact MemLp.toLp_sub (critical_continuous_memLp_cube v hv 2)
    (critical_continuous_memLp_cube w hw 2)

theorem physicalFieldL2_dist_sq (v w : Field) (hv : Continuous v) (hw : Continuous w) :
    dist (physicalFieldL2 v hv) (physicalFieldL2 w hw) ^ 2 = physicalEnergy (v - w) := by
  rw [dist_eq_norm, ← physicalFieldL2_sub v w hv hw]
  exact physicalFieldL2_norm_sq (v - w) (hv.sub hw)

def torusPhysicalFieldL2 (v : Field) (hv : Continuous v) : TorusVectorL2 :=
  WithLp.toLp 2 (fun i => torusDatumL2 v hv i)

theorem torusPhysicalFieldL2_fourierCoeff (v : Field) (hv : Continuous v) :
    torusVectorFourierCoeff (torusPhysicalFieldL2 v hv) = datumFourierCoeff v := by
  funext k i
  change UnitAddTorus.mFourierCoeff (torusDatumL2 v hv i) k = _
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact torusDatumL2_fourierBasis_repr v hv i k

theorem critical_Lp_sum_coe {ι : Type*} (s : Finset ι) (f : ι → PhysicalCubeL2) :
    ((∑ i ∈ s, f i : PhysicalCubeL2) : Field) =ᵐ[volume.restrict unitCube]
      (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero Vec 2 (volume.restrict unitCube))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add Filter.EventuallyEq.rfl ih)

theorem torusToPhysicalCubeL2_physicalField
    (v : Field) (hv : Continuous v) (hp : SpatialPeriodic v) :
    torusToPhysicalCubeL2 (torusPhysicalFieldL2 v hv) = physicalFieldL2 v hv := by
  let F : Fin 3 → PhysicalCubeL2 := fun i =>
    (criticalRealCoordinate i).compLpL 2 (volume.restrict unitCube)
      (criticalScalarCubePullback (torusDatumL2 v hv i))
  have hF (i : Fin 3) : F i =ᵐ[volume.restrict unitCube]
      (fun x => v x i • unitVector i) := by
    have hc := (criticalRealCoordinate i).coeFn_compLpL
      (criticalScalarCubePullback (torusDatumL2 v hv i))
    have hpull := Lp.coeFn_compMeasurePreserving (torusDatumL2 v hv i)
      criticalCubeTorusMap_measurePreserving
    have hdatum := criticalCubeTorusMap_measurePreserving.quasiMeasurePreserving.ae
      (torusDatumL2_coe v hv i)
    filter_upwards [hc, hpull, hdatum] with x hx hp' hd
    change F i x = _
    simp only [Function.comp_apply] at hp'
    change criticalScalarCubePullback (torusDatumL2 v hv i) x =
      torusDatumL2 v hv i (criticalCubeTorusMap x) at hp'
    rw [hx, hp', hd]
    change (torusDatumComponent v i (criticalCubeTorusMap x)).re • unitVector i = _
    exact congrArg (fun z : ℂ => z.re • unitVector i) (torusDatumComponent_mk v hp i x)
  have hsum : ((∑ i : Fin 3, F i : PhysicalCubeL2) : Field)
      =ᵐ[volume.restrict unitCube] v := by
    apply (critical_Lp_sum_coe Finset.univ F).trans
    have hall : ∀ᵐ x ∂volume.restrict unitCube, ∀ i : Fin 3, F i x = v x i • unitVector i :=
      ae_all_iff.mpr hF
    filter_upwards [hall] with x hx
    simp_rw [hx]
    exact sum_coordinate_unitVector (v x)
  apply Lp.ext
  have hdef : torusToPhysicalCubeL2 (torusPhysicalFieldL2 v hv) = ∑ i : Fin 3, F i := by
    simp only [torusToPhysicalCubeL2, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, F, torusPhysicalFieldL2]
    rfl
  rw [hdef]
  exact hsum.trans (physicalFieldL2_coe v hv).symm

def criticalInitialPhysicalL2 (a : CriticalSobolev 1) : PhysicalCubeL2 :=
  torusToPhysicalCubeL2 (criticalPhysicalL2 1 (by norm_num) a)

def CriticalRegularSolution.physicalL2 {ν : ℝ} {a : CriticalSobolev 1}
    (S : CriticalRegularSolution ν a) (t : ℝ) : PhysicalCubeL2 :=
  torusToPhysicalCubeL2 (criticalPhysicalL2 1 (by norm_num) (S.critical t))

theorem CriticalRegularSolution.physicalL2_continuous
    {ν : ℝ} {a : CriticalSobolev 1} (S : CriticalRegularSolution ν a) :
    ContinuousOn S.physicalL2 (Ici 0) :=
  torusToPhysicalCubeL2.continuous.comp_continuousOn
    ((criticalPhysicalL2 1 (by norm_num)).continuous.comp_continuousOn S.continuous)

theorem CriticalRegularSolution.physicalL2_eq_field
    {ν : ℝ} {a : CriticalSobolev 1} (S : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 < t) :
    S.physicalL2 t = physicalFieldL2 (S.flow.velocity t)
      (S.flow.velocity_smoothSigmaZero t ht).smooth.continuous := by
  have hs := S.flow.velocity_smoothSigmaZero t ht
  have hc : criticalPhysicalL2 1 (by norm_num) (S.critical t) =
      torusPhysicalFieldL2 (S.flow.velocity t) hs.smooth.continuous := by
    apply torusVectorFourierCoeff_injective
    rw [criticalPhysicalL2_fourierCoeff, torusPhysicalFieldL2_fourierCoeff]
    change criticalCoeff 1 (S.critical t) = datumFourierCoeff
      (smoothFourierSynthesis (S.flow.state 0 t).val)
    rw [datumFourierCoeff_smoothFourierSynthesis _
      (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (S.flow.state_all_mem t ht)) (S.flow.reality t ht)]
    exact (S.coefficient_agreement t ht).symm
  change torusToPhysicalCubeL2 (criticalPhysicalL2 1 (by norm_num) (S.critical t)) = _
  rw [hc]
  exact torusToPhysicalCubeL2_physicalField _ hs.smooth.continuous hs.periodic

theorem CriticalRegularSolution.physicalL2_initial_trace
    {ν : ℝ} {a : CriticalSobolev 1} (S : CriticalRegularSolution ν a) :
    Tendsto S.physicalL2 (𝓝[>] (0 : ℝ)) (𝓝 (criticalInitialPhysicalL2 a)) := by
  have h := (S.physicalL2_continuous 0 (by change (0 : ℝ) ≤ 0; exact le_rfl)).mono
    (Ioi_subset_Ici_self : Ioi (0 : ℝ) ⊆ Ici 0)
  simpa only [CriticalRegularSolution.physicalL2, S.initial, criticalInitialPhysicalL2] using h

/-- Literal strong L2 trace of the real physical velocity against the
canonical real cube representative of the critical datum. -/
theorem CriticalRegularSolution.physical_eLpNorm_initial_trace
    {ν : ℝ} {a : CriticalSobolev 1} (S : CriticalRegularSolution ν a) :
    Tendsto (fun t => eLpNorm
      (S.flow.velocity t - (criticalInitialPhysicalL2 a : Field)) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (S.physicalL2_initial_trace.sub_const (criticalInitialPhysicalL2 a)).enorm
  have hzero : Tendsto (fun t => ‖S.physicalL2 t - criticalInitialPhysicalL2 a‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [sub_self, enorm_zero] using h
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hfield : S.physicalL2 t =ᵐ[volume.restrict unitCube] S.flow.velocity t := by
    rw [S.physicalL2_eq_field t ht]
    exact physicalFieldL2_coe _ _
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact (Lp.coeFn_sub _ _).trans (hfield.sub Filter.EventuallyEq.rfl)

end
end SingularClosure
