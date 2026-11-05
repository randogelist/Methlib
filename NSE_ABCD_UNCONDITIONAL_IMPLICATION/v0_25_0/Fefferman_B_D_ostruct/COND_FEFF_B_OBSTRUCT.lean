import PeriodicShearAnalytic
import PeriodicShearTrace
import PeriodicShearComparison

noncomputable section
open Set Fefferman Fefferman.ConcreteReal

namespace CondFeffB

/-- Every positive viscosity has the same initial-time Fourier obstruction. -/
theorem shearTrace_not_analytic {ν : ℝ} (hν : 0 < ν) :
    ¬ AnalyticWithinAt ℝ (fun t => shearProfile ν t 0) (Ici 0) 0 := by
  intro h
  obtain ⟨C, M, hC, hM, hbound⟩ := analyticRight_normalized_bound h
  apply PeriodicShear.moment_no_factorial_bound (4 * Real.pi ^ 2 * ν) (by positivity)
  refine ⟨C, M, hC, hM, ?_⟩
  intro m
  have hfac : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hcoeff := (div_le_iff₀ hfac).mp (hbound m)
  rw [abs_shearTraceJet_eq_moment hν m] at hcoeff
  calc
    _ ≤ (C * M ^ m) * (m.factorial : ℝ) := hcoeff
    _ = _ := by ring

/-- No velocity/pressure pair meeting the v0.25.0 periodic specification has this trace. -/
theorem shearDatum_no_periodic_witness (ν : PositiveViscosity realAnalysis) :
    ¬ hasGlobalSolution realAnalysis .periodic ν shearDatum (zeroForce realAnalysis) := by
  rintro ⟨s, hs⟩
  have htrace := candidate_origin_eq_shear hs
  have hsm : vectorSmooth realAnalysis s.velocity := hs.2.2.2.2.1.1
  have h0 : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.velocity z.1 z.2 0)
      {z : RSpace × ℝ | 0 ≤ z.2} := hsm 0
  have ha : AnalyticWithinAt ℝ (fun r : ℝ => s.velocity (0 : RSpace) r (0 : Fin 3))
      (Ici (0 : ℝ)) 0 :=
    analyticTimeTrace (F := fun z : RSpace × ℝ => s.velocity z.1 z.2 (0 : Fin 3))
      (0 : RSpace) h0
  have heq : EqOn (fun t => shearProfile ν.val t 0) (fun t => s.velocity 0 t 0) (Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
    have hv := congrFun (htrace t ht0) (0 : Fin 3)
    simpa only [shearVelocity_first, Pi.zero_apply] using hv.symm
  exact shearTrace_not_analytic ν.property
    (ha.congr heq (heq (show (0 : ℝ) ∈ Ici 0 from self_mem_Ici)))

theorem periodic_endpoint_obstruct : ¬ PeriodicZeroForceGlobalRegularity := by
  intro h
  let ν : PositiveViscosity realAnalysis := ⟨1, by change (0 : ℝ) < 1; norm_num⟩
  exact shearDatum_no_periodic_witness ν (h ν shearDatum shearDatum_admissible)

/-- The named root is the negation of the literal, analytic package B. -/
theorem COND_FEFF_B_OBSTRUCT : ¬ Fefferman.B realAnalysis := by
  intro hB
  exact periodic_endpoint_obstruct (PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B.mpr hB)

end CondFeffB
