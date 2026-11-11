import SingularClosure.FiniteParseval
import SingularClosure.GalerkinEnergyIntegral

/-!
# Exact conversion of the physical AX6 budget

The concrete six-channel Pythagoras identity eliminates the reconstruction
factor. Continuity of the actual coefficient trajectory supplies time
integrability before conversion to a real interval integral.
This is an auxiliary to endpoint 7, not its strong-bounds conclusion.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal Interval

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.coefficientSquareBudget_integrableOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (T : ℝ) :
    IntegrableOn (fun t => (coefficientDissipation N (g.coeff t)) ^ 2)
      (Icc (0 : ℝ) T) volume :=
  ((g.coefficientDissipation_continuousOn.mono
    (fun t ht => ht.1)).pow 2).integrableOn_compact isCompact_Icc

theorem GalerkinSolution.budget6_eq_ofReal_intervalIntegral
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T) :
    budget6 N g.coeff T = ENNReal.ofReal
      (∫ t in (0 : ℝ)..T, (coefficientDissipation N (g.coeff t)) ^ 2) := by
  rw [SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ]
  have hpoint :
      (fun t => (physicalEnstrophy (finiteSynthesis N (g.coeff t))) ^ 2)
        =ᵐ[volume.restrict (Icc (0 : ℝ) T)]
      (fun t => ENNReal.ofReal ((coefficientDissipation N (g.coeff t)) ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [FINITE_PHYSICAL_ENSTROPHY_PARSEVAL N (g.coeff t) (g.real_symmetry t ht.1),
      ENNReal.ofReal_pow (coefficientDissipation_nonneg N (g.coeff t))]
  rw [lintegral_congr_ae hpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (g.coefficientSquareBudget_integrableOn T)
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))]
  rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

theorem AX6_EXACT_REAL_SQUARE_BUDGET (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      IntervalIntegrable (fun t => (coefficientDissipation N (g.coeff t)) ^ 2)
        volume 0 T ∧
      (∫ t in (0 : ℝ)..T, (coefficientDissipation N (g.coeff t)) ^ 2) ≤ M := by
  obtain ⟨M, hM⟩ := hAX6 ν hν a ha T hT
  refine ⟨(M : ℝ), M.property, ?_⟩
  intro N hN g
  constructor
  · exact ((g.coefficientDissipation_continuousOn.mono
      (fun t ht => ht.1)).pow 2).intervalIntegrable_of_Icc hT.le
  · apply ENNReal.ofReal_le_coe.mp
    rw [← g.budget6_eq_ofReal_intervalIntegral hT.le]
    exact hM N hN g

theorem AX6_EXACT_PHYSICAL_SQUARE_BUDGET (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ≥0, ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫⁻ t in Icc (0 : ℝ) T, (physicalEnstrophy (g.velocity t)) ^ 2) ≤
        (M : ℝ≥0∞) := by
  obtain ⟨M, hM⟩ := hAX6 ν hν a ha T hT
  refine ⟨M, ?_⟩
  intro N hN g
  change (∫⁻ t in Icc (0 : ℝ) T,
    (physicalEnstrophy (finiteSynthesis N (g.coeff t))) ^ 2) ≤ _
  rw [← SIX_CHANNEL_FINITE_SQUARE_BUDGET_EQ]
  exact hM N hN g

end

end SingularClosure
