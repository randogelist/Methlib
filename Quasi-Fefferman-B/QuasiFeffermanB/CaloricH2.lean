import QuasiFeffermanB.CaloricPhysicalControl
import QuasiFeffermanB.CaloricSmoothing

/-! The actual caloric Galerkin budget supplies the positive-time H2 seed. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem CALORIC_H1_GALERKIN_H2_BUDGET
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 a)) (S : ℝ)
    (hbudget : ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N),
      ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S)
    (τ T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N),
      (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ B := by
  let L : ℝ := ‖a‖ ^ 2 * Real.exp (S / ν)
  have hL : 0 ≤ L := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨3 * L * (T - τ) + L / ν,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sub_nonneg.mpr hτT))
      (div_nonneg hL hν.le), ?_⟩
  apply GALERKIN_H2_SEED_OF_ENSTROPHY_ACCUMULATION ν hν
    (fun N => finiteSynthesis N (criticalCoeff 2 a)) τ T hτ hτT L hL
  intro N g t ht
  have ht0 : 0 ≤ t := hτ.le.trans ht.1
  have hacc := CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION ν hν a hreal S hbudget
    T (hτ.le.trans hτT) N g t ⟨ht0, ht.2⟩
  have hZi : IntervalIntegrable (fun r => coefficientLaplacianSquare N (g.coeff r))
      volume 0 t :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun r hr => hr.1)).intervalIntegrable_of_Icc ht0
  have hmono : (∫ r in τ..t, coefficientLaplacianSquare N (g.coeff r)) ≤
      ∫ r in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff r) :=
    intervalIntegral.integral_mono_interval hτ.le ht.1 le_rfl
      (Filter.Eventually.of_forall (fun r => coefficientLaplacianSquare_nonneg N (g.coeff r))) hZi
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmono hν.le)).trans hacc

/-- The caloric budget discharges the all-order positive-time seed for H1
data. The H0 Galerkin limit and convergence remain the compactness input. -/
theorem CALORIC_H1_POSITIVE_FLOW_OF_GALERKIN_LIMIT
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 a)) (S : ℝ)
    (hbudget : ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N),
      ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 2 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)) :
    ∃ L : CriticalPositiveSobolevFlow ν,
      (∀ t : ℝ, 0 < t → L.state 0 t = u t) ∧
      PositiveSmoothNSE ν L.velocity L.pressure := by
  apply GALERKIN_POSITIVE_FLOW_OF_H2_SEED ν hν
    (fun N => finiteSynthesis N (criticalCoeff 2 a))
    (fun σ T hσ hσT => CALORIC_H1_GALERKIN_H2_BUDGET ν hν a hreal S hbudget σ T hσ hσT.le)
    φ hφ g u hu hconv

end
end QuasiFeffermanB
