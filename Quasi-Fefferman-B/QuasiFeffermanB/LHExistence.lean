import QuasiFeffermanB.EnergyTimeCompactness
import QuasiFeffermanB.Semantics

/-! Energy-level Galerkin extraction for the arbitrary-L2 existence proof.
This file supplies an actual L2-valued limit and strong L2-in-time convergence
from uniform initial energy. The physical Leray--Hopf assembly is a subsequent
proof obligation; no existence conclusion is inserted as a field or axiom. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem galerkin_H1_time_energy_bound
    {ν : ℝ} (hν : 0 < ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (R T : ℝ) (hT : 0 ≤ T)
    (hinit : coefficientEnergy N (g.coeff 0) ≤ R ^ 2) :
    (∫ t in (0 : ℝ)..T, ‖g.sobolevState 1 t‖ ^ 2) ≤
      T * R ^ 2 + R ^ 2 / (2 * ν) := by
  have hEc : ContinuousOn (fun t => coefficientEnergy N (g.coeff t)) (Icc (0 : ℝ) T) :=
    g.coefficientEnergy_continuousOn.mono (fun t ht => ht.1)
  have hEi := hEc.intervalIntegrable_of_Icc hT
  have hDi := g.coefficientDissipation_intervalIntegrable hT
  have hE : (∫ t in (0 : ℝ)..T, coefficientEnergy N (g.coeff t)) ≤ T * R ^ 2 := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..T, R ^ 2 :=
        intervalIntegral.integral_mono_on hT hEi intervalIntegrable_const
          (fun t ht => (g.coefficientEnergy_le_initial hν.le ht.1).trans hinit)
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hD : (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t)) ≤
      R ^ 2 / (2 * ν) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).mpr
    have he := g.coefficientEnergy_integral_identity hT
    have hn := coefficientEnergy_nonneg N (g.coeff T)
    nlinarith
  have heq (t : ℝ) :
      ‖g.sobolevState 1 t‖ ^ 2 =
        coefficientEnergy N (g.coeff t) + coefficientDissipation N (g.coeff t) :=
    finiteSobolev_H1_norm_sq N (g.coeff t)
  simp_rw [heq]
  rw [intervalIntegral.integral_add hEi hDi]
  exact add_le_add hE hD

theorem galerkin_critical_zero_norm_sq {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) :
    ‖g.criticalState 0 t‖ ^ 2 = coefficientEnergy N (g.coeff t) := by
  unfold GalerkinSolution.criticalState
  rw [criticalFiniteSobolev_norm_sq]
  simp only [zpow_zero, one_mul, coefficientEnergy]

/-- A bounded physical-energy Galerkin sequence has a genuine L2-valued
pointwise coefficient limit, with uniform convergence of every coefficient. -/
theorem ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ u : Icc (0 : ℝ) T → TorusSobolev 0, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ k i, TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i)
        (fun t => (u t).val k i) atTop := by
  classical
  obtain ⟨c, φ, hφ, hconv⟩ :=
    ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE ν hν a N g R T hR hT hinit
  have hex (t : Icc (0 : ℝ) T) :
      ∃ v : CriticalSobolev 0, criticalCoeff 0 v = (fun k i => c (k, i) t) ∧ ‖v‖ ≤ R := by
    apply criticalSobolev_limit_mem_and_norm_le (l := (atTop : Filter ℕ)) 0
      (fun n => (g (φ n)).criticalState 0 t.val) (fun k i => c (k, i) t) R
    · intro n
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      rw [galerkin_critical_zero_norm_sq]
      exact ((g (φ n)).coefficientEnergy_le_initial hν t.property.1).trans (hinit (φ n))
    · intro k i
      have heq (n : ℕ) :
          criticalCoeff 0 ((g (φ n)).criticalState 0 t.val) = (g (φ n)).coeff t.val :=
        (g (φ n)).criticalState_coeff 0 t.property.1
      simpa only [heq] using (hconv k i).tendsto_at t
  choose u hu hb using hex
  refine ⟨fun t => criticalH0Equiv (u t), φ, hφ, ?_, ?_⟩
  · intro t
    simpa only [criticalH0Equiv.norm_map] using hb t
  · intro k i
    have hleft :
        (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i) =
        (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).coeff t.val k i) := by
      funext n t
      rw [(g (φ n)).sobolevState_coeff 0 t.property.1]
    have hright :
        (fun t : Icc (0 : ℝ) T => (criticalH0Equiv (u t)).val k i) =
        (fun t : Icc (0 : ℝ) T => c (k, i) t) := by
      funext t
      rw [criticalH0Equiv_coeff, hu t]
    rw [hleft, hright]
    exact hconv k i

/-- The ordinary L2 energy law suffices for actual strong spacetime-L2
compactness of the Galerkin sequence. -/
theorem ENERGY_GALERKIN_L2H0_SUBSEQUENCE
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ u : Icc (0 : ℝ) T → TorusSobolev 0, ∃ v : EnergyTimeH0L2 T,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ t, ‖u t‖ ≤ R) ∧
      (∀ k i, TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i)
        (fun t => (u t).val k i) atTop) ∧
      Tendsto (fun n => (g (φ n)).energyTimeH0L2 T) atTop (𝓝 v) := by
  obtain ⟨u, φ, hφ, hb, hc⟩ :=
    ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT ν hν.le a N g R T hR hT hinit
  let B : ℝ := T * R ^ 2 + R ^ 2 / (2 * ν)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget (n : ℕ) :
      (∫ t in (0 : ℝ)..T, ‖(g (φ n)).sobolevState 1 t‖ ^ 2) ≤ B :=
    galerkin_H1_time_energy_bound hν (g (φ n)) R T hT (hinit (φ n))
  obtain ⟨v, hv⟩ := ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM
    ν (fun n => a (φ n)) (fun n => N (φ n)) (fun n => g (φ n))
    T B hT hB u hc hbudget
  exact ⟨u, v, φ, hφ, hb, hc, hv⟩

end
end QuasiFeffermanB

