import QuasiFeffermanB.CaloricFlowControl

/-! A finite datumwise caloric Galerkin budget constructs an actual global
smooth positive-time NSE flow and identifies every Leray--Hopf competitor.
The numerical heat-admission estimate is separate from this analytic edge. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval ENNReal

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem CALORIC_H1_REGULARITY_OF_FINITE_CHI0_BUDGET
    (ν : ℝ) (hν : 0 < ν) (b : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 b))
    (hsol : SpectralSolenoidal (criticalCoeff 2 b))
    (hzero : SpectralMeanZero (criticalCoeff 2 b))
    (S : ℝ)
    (hbudget : ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 b)) N),
      ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S) :
    ∃ L : CriticalPositiveSobolevFlow ν,
      PositiveSmoothNSE ν L.velocity L.pressure ∧
      Tendsto (fun t => eLpNorm
        (L.velocity t - (criticalInitialPhysicalL2
          (criticalSobolevLower 1 2 (by norm_num) b) : Field)) 2
        (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ T : ℝ, 0 < T → MemLp
        (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T))) ∧
      (∀ t : ℝ, 0 < t → physicalDissipation (L.velocity t) ≤
        ‖b‖ ^ 2 * Real.exp (S / ν)) ∧
      (∀ (v : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)),
        CriticalLerayHopf ν
          (criticalInitialPhysicalL2 (criticalSobolevLower 1 2 (by norm_num) b)) v G →
        ∀ t : ℝ, 0 < t → v t =ᵐ[volume.restrict unitCube] L.velocity t) := by
  let a : CriticalSobolev 1 := criticalSobolevLower 1 2 (by norm_num) b
  have hac : criticalCoeff 1 a = criticalCoeff 2 b := criticalSobolevLower_coeff _ _ _ _
  have har : SpectralReality (criticalCoeff 1 a) := by rw [hac]; exact hreal
  have has : SpectralSolenoidal (criticalCoeff 1 a) := by rw [hac]; exact hsol
  have haz : SpectralMeanZero (criticalCoeff 1 a) := by rw [hac]; exact hzero
  let g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (n + 1) (criticalCoeff 1 a)) (n + 1) :=
    criticalDatumGalerkinFamily ν hν.le a har has
  let D : ℝ := ‖b‖ ^ 2 * Real.exp (S / ν)
  have hD0 : 0 ≤ D := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hacc (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
      coefficientDissipation (n + 1) ((g n).coeff T) +
        ν * (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare (n + 1) ((g n).coeff t)) ≤ D := by
    have h := CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION ν hν b hreal S hbudget T hT
    rw [← hac] at h
    exact h (n + 1) (g n) T ⟨hT, le_rfl⟩
  have hD (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      coefficientDissipation (n + 1) ((g n).coeff t) ≤ D := by
    have hI : 0 ≤ ∫ r in (0 : ℝ)..t, coefficientLaplacianSquare (n + 1) ((g n).coeff r) :=
      intervalIntegral.integral_nonneg_of_forall ht
        (fun r => coefficientLaplacianSquare_nonneg _ _)
    have h := hacc n t ht
    nlinarith [mul_nonneg hν.le hI]
  have hZ (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare (n + 1) ((g n).coeff t)) ≤ D / ν := by
    apply (le_div_iff₀ hν).2
    have h := hacc n T hT
    nlinarith [coefficientDissipation_nonneg (n + 1) ((g n).coeff T)]
  obtain ⟨u, φ, hφ, hu, hu0, hub, hconv⟩ :=
    GALERKIN_CRITICAL_COMPACTNESS_OF_ENSTROPHY ν hν a har haz g D hD0 hD hZ
  let gs : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1) := fun n => g (φ n)
  let u0 : ℝ → TorusSobolev 0 := fun t => criticalToTorusH0 1 (by norm_num) (u t)
  have hu0c : ContinuousOn u0 (Ici 0) :=
    (criticalToTorusH0 1 (by norm_num)).continuous.comp_continuousOn hu
  have hseed : ∀ σ T : ℝ, 0 < σ → σ < T →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ)
        (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
          (∫ t in σ..T, highOrderEnergy 2 N (g.coeff t)) ≤ B := by
    intro σ T hσ hσT
    rw [hac]
    exact CALORIC_H1_GALERKIN_H2_BUDGET ν hν b hreal S hbudget σ T hσ hσT.le
  obtain ⟨L, hL, hNSE⟩ := GALERKIN_POSITIVE_FLOW_OF_H2_SEED ν hν
    (fun N => finiteSynthesis N (criticalCoeff 1 a)) hseed φ hφ gs u0 hu0c
    (fun T _ => hconv T)
  have hLc (t : ℝ) (ht : 0 < t) : (L.state 0 t).val = criticalCoeff 1 (u t) := by
    rw [hL t ht]
    exact criticalToTorusH0_coeff _ _ _
  have htrace := POSITIVE_FLOW_STRONG_PHYSICAL_TRACE_OF_CRITICAL_CURVE a L u hu hu0 hLc
  have henergy (t : ℝ) (ht : 0 < t) : physicalEnergy (L.velocity t) ≤ (D + 1) ^ 2 :=
    POSITIVE_FLOW_PHYSICAL_ENERGY_OF_CRITICAL_BOUND L u hLc (D + 1) hub t ht
  have hdiss (t : ℝ) (ht : 0 < t) : physicalDissipation (L.velocity t) ≤ D :=
    POSITIVE_FLOW_DISSIPATION_OF_GALERKIN_BOUND ν
      (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ gs L D hD0 u0 hL
      (fun n r hr => hD (φ n) r hr) (fun T _ => hconv T) t ht
  have hSerrin (T : ℝ) (_hT : 0 < T) :
      MemLp (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)) :=
    POSITIVE_FLOW_SERRIN_OF_UNIFORM_PHYSICAL_BOUNDS L ((D + 1) ^ 2) D henergy hdiss T
  refine ⟨L, hNSE, htrace, hSerrin, hdiss, ?_⟩
  intro v G hv
  exact POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN ν hν
    (criticalInitialPhysicalL2 a) L htrace hSerrin v G hv

end
end QuasiFeffermanB
