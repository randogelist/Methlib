import SingularClosure.H12Frontier.ReplayEnergy
import SingularClosure.CriticalPositiveTimeSeed
import SingularClosure.CriticalPositiveTimeHighOrder
import SingularClosure.CriticalPositiveLimit

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem positiveEnstrophy (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY
  let M : ℝ := ‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖))
  let κ : ℝ := C / ν ^ 3
  have hM : 0 ≤ M := div_nonneg (pow_nonneg (norm_nonneg a) 4)
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  have hκ : 0 ≤ κ := div_nonneg hC.le (pow_nonneg hν.le 3)
  have hT : 0 ≤ T := hτ.le.trans hτT
  refine ⟨Real.sqrt (M / τ) * Real.exp (κ * M),
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro N g
  let y : ℝ → ℝ := fun t => coefficientDissipation N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (coefficientLaplacianSquare N (g.coeff t))
  let d : ℝ → ℝ := fun t => coefficientEnstrophyRate ν N (g.coeff t)
  have hy : ContinuousOn y (Icc 0 T) :=
    g.coefficientDissipation_continuousOn.mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      g.coefficientLaplacianSquare_continuousOn).mono (fun t ht => ht.1)
  have hd : ContinuousOn d (Icc 0 T) :=
    g.coefficientEnstrophyRate_continuousOn.mono (fun t ht => ht.1)
  have hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t := by
    intro t ht
    exact (g.coefficientDissipation_hasDerivWithinAt ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)
  have hcubic : ∀ t ∈ Ioo 0 T,
      d t + ν * z t ^ 2 ≤ κ * y t ^ 3 := by
    intro t ht
    obtain ⟨d', hd', hb⟩ := hineq ν hν _ N g t ht.1.le
    have heq : d t = d' := (hderiv t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds ht.1))
    dsimp only [z]
    rw [Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff t)), heq]
    exact hb
  have hbudget : (∫ t in (0 : ℝ)..T, y t ^ 2) ≤ M :=
    g.critical_square_budget_of_differential_inequality hT cert.positive.le
      (norm_nonneg a) hsmall (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
      (fun t ht => (differentialInequality cert g) ht.1)
  have hacc := CUBIC_POSITIVE_TIME_ACCUMULATION hν hκ hτ hτT hM hy hz hd
    (fun t _ => coefficientDissipation_nonneg N (g.coeff t)) hderiv hcubic hbudget
  have hzsq (s : ℝ) : z s ^ 2 = coefficientLaplacianSquare N (g.coeff s) :=
    Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff s))
  intro t ht
  simpa only [y, hzsq] using hacc t ht

theorem positiveH2 (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
        (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ S := by
  obtain ⟨L, hL, hacc⟩ := (positiveEnstrophy cert)
    ν hν a hreal hsmall τ hτ T hτT
  refine ⟨3 * L * (T - τ) + L / ν,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sub_nonneg.mpr hτT))
      (div_nonneg hL hν.le), ?_⟩
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

theorem positiveAllOrders (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  GALERKIN_POSITIVE_TIME_ALL_ORDERS ν hν
    (fun N => finiteSynthesis N (criticalCoeff 1 a))
    (fun σ T hσ hσT => (positiveH2 cert) ν hν a hreal hsmall σ hσ T hσT.le)
    m τ T hτ hτT

theorem positiveFlow (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)) :
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t := by
  apply CRITICAL_POSITIVE_FLOW_OF_GALERKIN_LIMIT ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g u hu hconv
  intro s τ T hτ hτT
  obtain ⟨B, hB, hb⟩ := (positiveAllOrders cert) ν hν a hreal hsmall s τ T hτ hτT
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

end
end SingularClosure.H12Frontier.Replay
