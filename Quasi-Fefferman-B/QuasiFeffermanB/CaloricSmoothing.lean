import SingularClosure.CriticalPositiveTimeHighOrder
import SingularClosure.CriticalPositiveLimit

/-!
Datumwise positive-time smoothing of actual Galerkin limits.
No universal AX6Statement and no chosen small-critical constant is used.
The concrete enstrophy/Laplacian seed remains an explicit quantitative input.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- A positive-time enstrophy/Laplacian accumulation yields the H2 seed
required by the existing all-order Galerkin bootstrap. -/
theorem GALERKIN_H2_SEED_OF_ENSTROPHY_ACCUMULATION
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field)
    (τ T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T)
    (L : ℝ) (hL : 0 ≤ L)
    (hacc : ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L) :
    ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
      (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤
        3 * L * (T - τ) + L / ν := by
  intro N g
  have hy (t : ℝ) (ht : t ∈ Icc τ T) : coefficientDissipation N (g.coeff t) ≤ L := by
    have h := hacc N g t ht
    have hz : 0 ≤ ∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s) :=
      intervalIntegral.integral_nonneg_of_forall ht.1
        (fun s => coefficientLaplacianSquare_nonneg N (g.coeff s))
    nlinarith [mul_nonneg hν.le hz]
  have hZi : IntervalIntegrable (fun t => coefficientLaplacianSquare N (g.coeff t))
      volume τ T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => hτ.le.trans ht.1)).intervalIntegrable_of_Icc hτT
  have hZ : (∫ t in τ..T, coefficientLaplacianSquare N (g.coeff t)) ≤ L / ν := by
    apply (le_div_iff₀ hν).2
    have h := hacc N g T ⟨hτT, le_rfl⟩
    nlinarith [coefficientDissipation_nonneg N (g.coeff T)]
  have hH2i : IntervalIntegrable (fun t => highOrderEnergy 2 N (g.coeff t)) volume τ T :=
    ((g.highOrderEnergy_continuousOn 2).mono
      (fun t ht => hτ.le.trans ht.1)).intervalIntegrable_of_Icc hτT
  have hpoint (t : ℝ) (ht : t ∈ Icc τ T) :
      highOrderEnergy 2 N (g.coeff t) ≤ 3 * L + coefficientLaplacianSquare N (g.coeff t) := by
    have ht0 : 0 ≤ t := hτ.le.trans ht.1
    have heq : highOrderEnergy 2 N (g.coeff t) =
        coefficientEnergy N (g.coeff t) + 2 * coefficientDissipation N (g.coeff t) +
          coefficientLaplacianSquare N (g.coeff t) := by
      rw [highOrderEnergy_eq_sobolev_norm_sq]
      change ‖g.sobolevState 2 t‖ ^ 2 = _
      rw [g.sobolevState_H2_square_eq ht0, g.physicalH2Square_eq ht0]
    rw [heq]
    have henergy := coefficientEnergy_le_dissipation N (g.coeff t)
    linarith [hy t ht]
  calc
    _ ≤ ∫ t in τ..T, 3 * L + coefficientLaplacianSquare N (g.coeff t) :=
      intervalIntegral.integral_mono_on hτT hH2i (intervalIntegrable_const.add hZi) hpoint
    _ = (T - τ) * (3 * L) + ∫ t in τ..T, coefficientLaplacianSquare N (g.coeff t) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
        intervalIntegral.integral_const]
      rfl
    _ ≤ (T - τ) * (3 * L) + L / ν := add_le_add (le_refl _) hZ
    _ = _ := by ring

/-- An actual H0 Galerkin limit with the integrated H2 seed has an actual
positive-time Sobolev NSE flow and normalized smooth physical pressure. -/
theorem GALERKIN_POSITIVE_FLOW_OF_H2_SEED
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field)
    (hseed : ∀ σ T : ℝ, 0 < σ → σ < T →
      ∃ S : ℝ, 0 ≤ S ∧ ∀ (N : ℕ) (g : GalerkinSolution ν (a N) N),
        (∫ s in σ..T, highOrderEnergy 2 N (g.coeff s)) ≤ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν (a (φ n + 1)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)) :
    ∃ L : CriticalPositiveSobolevFlow ν,
      (∀ t : ℝ, 0 < t → L.state 0 t = u t) ∧
      PositiveSmoothNSE ν L.velocity L.pressure := by
  have hbound : ∀ (s : ℕ) (τ T : ℝ), 0 < τ → τ < T →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (t : ℝ), t ∈ Icc τ T →
        ‖(g n).sobolevState s t‖ ≤ B := by
    intro s τ T hτ hτT
    obtain ⟨B, hB, hb⟩ := GALERKIN_POSITIVE_TIME_ALL_ORDERS ν hν a hseed s τ T hτ hτT
    refine ⟨B + 1, by linarith, ?_⟩
    intro n t ht
    have h := hb (φ n + 1) (g n) t ht
    have hi : 0 ≤ ∫ z in τ..t, highOrderEnergy (s + 1) (φ n + 1) ((g n).coeff z) :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun z => highOrderEnergy_nonneg _ _ _)
    have hn : ‖(g n).sobolevState s t‖ ^ 2 ≤ B := by
      have heq : highOrderEnergy s (φ n + 1) ((g n).coeff t) =
          ‖(g n).sobolevState s t‖ ^ 2 := highOrderEnergy_eq_sobolev_norm_sq _ _ _
      rw [← heq]
      nlinarith [mul_nonneg hν.le hi]
    nlinarith [sq_nonneg (‖(g n).sobolevState s t‖ - 1)]
  obtain ⟨L, hL⟩ := CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT ν
    (fun n => a (φ n + 1)) φ hφ g u hu hconv hbound
  exact ⟨L, hL, CRITICAL_POSITIVE_PHYSICAL_NSE L⟩

end
end QuasiFeffermanB
