import PeriodicShearMomentum
import PeriodicShearEnergyTime
import PeriodicShearFluxRegularity
import PeriodicShearLocalBalance

noncomputable section
open Fefferman Fefferman.ConcreteReal Set MeasureTheory
open scoped BigOperators

namespace CondFeffB

/-- A local differential bound integrates on a period cell with no boundary term. -/
theorem cellIntegral_bound_of_flux {F : RSpace → RVector} {D E : RSpace → ℝ} {K : ℝ}
    (hF : ∀ j, ContDiff ℝ 1 (fun x => F x j))
    (hp : ∀ x j, F (unitShift realAnalysis x j) j = F x j)
    (hD : IntegrableOn D centeredCell) (hE : IntegrableOn E centeredCell)
    (hb : ∀ x, D x ≤ fluxDivergence F x + K * E x) :
    (∫ x in centeredCell, D x) ≤ K * ∫ x in centeredCell, E x := by
  have hdiv : Continuous (fluxDivergence F) := by
    change Continuous (fun x : RSpace => ∑ j : Fin 3, spatialDerivative j (fun y => F y j) x)
    refine continuous_finsetSum
      (f := fun (j : Fin 3) (x : RSpace) => spatialDerivative j (fun y => F y j) x)
      Finset.univ (fun j _ => ?_)
    exact ((hF j).continuous_fderiv one_ne_zero).clm_apply
      (show Continuous (fun _ : RSpace => basisDirection j) from continuous_const)
  have hdivI : IntegrableOn (fluxDivergence F) centeredCell :=
    hdiv.continuousOn.integrableOn_compact (show IsCompact centeredCell from isCompact_Icc)
  have hKE : IntegrableOn (fun x => K * E x) centeredCell := hE.const_mul K
  have hz : (∫ x in centeredCell, fluxDivergence F x) = 0 :=
    integral_periodic_fluxDivergence F hF hp
  calc
    (∫ x in centeredCell, D x) ≤ ∫ x in centeredCell, fluxDivergence F x + K * E x :=
      setIntegral_mono_on hD (hdivI.add hKE) (show MeasurableSet centeredCell from measurableSet_Icc)
        (fun x _ => hb x)
    _ = K * ∫ x in centeredCell, E x := by rw [integral_add hdivI hKE, hz, zero_add, integral_const_mul]

/-- For the physical difference field the only production term is the
background shear slope. Diffusion appears with a nonpositive sign. -/
theorem candidate_pointwise_energy_bound {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) (x : RSpace) :
    energyTimeDensity s.velocity (shearVelocity ν.val) t x ≤
      fluxDivergence (candidateFlux s ν.val t) x +
      shearSlopeBound * sqDifference s.velocity (shearVelocity ν.val) t x := by
  let W := relativeVelocity s.velocity ν.val
  let U := s.velocity
  let P := fun y : RSpace => s.pressure y t
  let slope := shearSlope ν.val t (x 1)
  let D := fun i : Fin 3 =>
    componentTimeDerivative U x t i - componentTimeDerivative (shearVelocity ν.val) x t i
  let DU : Fin 3 → RVector := fun j i => dxV U j i t x
  let DW : Fin 3 → RVector := fun j i => dxV W j i t x
  let DDW : Fin 3 → RVector := fun j i => dxxV W j i t x
  let DP := fun j => spatialDerivative j P x
  have hPDE (i : Fin 3) : D i + (∑ j, U x t j * DW j i) +
      (if i = 0 then W x t 1 * slope else 0) = ν.val * (∑ j, DDW j i) - DP i := by
    have h := relative_momentum hs ht x i
    rw [deriv_relative hs ht x i] at h
    simpa only [D, U, W, DW, DDW, DP, P, slope, componentTimeDerivative] using h
  have hbal := localEnergyBalance ν.val slope (P x) (U x t) (W x t) D DP DU DW DDW
    (candidate_divergence hs ht.le x) (relative_divergence hs ht.le x) hPDE
  obtain ⟨hU, hW, hDW, hP⟩ := candidateSlice_differentiable hs ht.le x
  have hslice : candidateDifference s ν.val t = (fun y : RSpace => W y t) := by
    funext y i
    rfl
  have hflux : fluxDivergence (candidateFlux s ν.val t) x =
      ∑ j, fluxDerivativeTerm ν.val (U x t) (W x t) (P x) DU DW DDW DP j := by
    change fluxDivergence
      (differenceFlux ν.val (fun y => U y t) (candidateDifference s ν.val t) P) x = _
    rw [hslice]
    -- The product rule now uses exactly the spatial slice of W on both sides.
    refine (fluxDivergence_differenceFlux ν.val (fun y => U y t) (fun y => W y t) P x
      hU hW hDW hP).trans ?_
    with_unfolding_all rfl
  rw [← hflux] at hbal
  have hprod := shearProduction_le slope shearSlopeBound (W x t)
    (abs_shearSlope_le (le_of_lt ν.property) ht.le (x 1))
  have hneg : 0 ≤ 2 * ν.val * (∑ j : Fin 3, ∑ i : Fin 3, (DW j i)^2) :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt ν.property))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  change (∑ i, 2 * W x t i * D i) ≤ fluxDivergence (candidateFlux s ν.val t) x +
    shearSlopeBound * (∑ i, (W x t i)^2)
  rw [hbal, sub_eq_add_neg _ (2 * slope * W x t 0 * W x t 1)]
  exact add_le_add (sub_le_self _ hneg) hprod

theorem candidate_cellEnergy_differential_bound {ν : PositiveViscosity realAnalysis}
    {a : RInitial} {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν a (zeroForce realAnalysis) s)
    {t : ℝ} (ht : 0 < t) :
    ∃ d : ℝ, HasDerivAt (cellEnergy s.velocity (shearVelocity ν.val)) d t ∧
      d ≤ shearSlopeBound * cellEnergy s.velocity (shearVelocity ν.val) t := by
  refine ⟨_, candidate_cellEnergy_hasDerivAt hs ht, ?_⟩
  have hu := jointVelocityContinuous_of_globalSolution hs
  have hv : JointVelocityContinuous (shearVelocity ν.val) :=
    shearVelocity_continuousOn ν.val (le_of_lt ν.property)
  have hc : Continuous (sqDifference s.velocity (shearVelocity ν.val) t) :=
    continuous_sqDifference (slice_continuous_of_joint hu ht.le) (slice_continuous_of_joint hv ht.le)
  exact cellIntegral_bound_of_flux (F := candidateFlux s ν.val t)
    (D := energyTimeDensity s.velocity (shearVelocity ν.val) t)
    (E := sqDifference s.velocity (shearVelocity ν.val) t) (K := shearSlopeBound)
    (candidateFlux_regular hs ht.le) (fun x j => candidateFlux_periodic hs ht.le x j j)
    (candidate_energyTimeDensity_integrableOn hs ht)
    (hc.continuousOn.integrableOn_compact (show IsCompact centeredCell from isCompact_Icc))
    (candidate_pointwise_energy_bound hs ht)

theorem candidate_origin_eq_shear {ν : PositiveViscosity realAnalysis}
    {s : Solution realAnalysis}
    (hs : globalSolution realAnalysis .periodic ν shearDatum (zeroForce realAnalysis) s) :
    ∀ t : ℝ, 0 ≤ t → s.velocity 0 t = shearVelocity ν.val 0 t := by
  have hu := jointVelocityContinuous_of_globalSolution hs
  have hv : JointVelocityContinuous (shearVelocity ν.val) :=
    shearVelocity_continuousOn ν.val (le_of_lt ν.property)
  have hini : ∀ x, s.velocity x 0 = shearVelocity ν.val x 0 :=
    fun x => (hs.2.2.1 x).trans (shearVelocity_initial ν.val x).symm
  intro t ht
  have hlocal (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) t) :
      ∃ d : ℝ, HasDerivAt (cellEnergy s.velocity (shearVelocity ν.val)) d r ∧
        d ≤ shearSlopeBound * cellEnergy s.velocity (shearVelocity ν.val) r :=
    candidate_cellEnergy_differential_bound hs (t := r) (Set.mem_Ioo.mp hr).1
  exact origin_eq_of_periodic_energy_ineq (u := s.velocity) (v := shearVelocity ν.val)
    (T := t) (K := shearSlopeBound) hu hv hini hlocal t (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)

end CondFeffB
