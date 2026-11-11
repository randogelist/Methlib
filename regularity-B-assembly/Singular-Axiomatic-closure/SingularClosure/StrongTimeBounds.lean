import SingularClosure.GalerkinTimeDerivative
import SingularClosure.ConvectionBound
import SingularClosure.StrongAccumulation

/-!
# Actual uniform Galerkin time-derivative bounds under AX6

Spatial and temporal regularity of the literal derivative are obtained from
its proved finite synthesis formula. The final bound is uniform in the cutoff
and the chosen trajectory, and assumes only AX6 and the physical datum.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff Interval

namespace SingularClosure

noncomputable section

theorem GalerkinSolution.timeDerivative_smooth
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (timeDerivative g.velocity t) := by
  rw [g.timeDerivative_eq_finiteSynthesis t ht]
  exact finiteSynthesis_contDiff N _

theorem GalerkinSolution.timeDerivative_continuousOn_forward
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun z : ℝ × Vec => timeDerivative g.velocity z.1 z.2)
      forwardSpacetime := by
  have hc : ContinuousOn (fun z : ℝ × Vec =>
      finiteSynthesis N (galerkinRhs ν N (g.coeff z.1)) z.2) forwardSpacetime := by
    simp_rw [finiteSynthesis_eq_sum_unitVector]
    apply continuousOn_finset_sum
    intro i _
    have hsum : ContinuousOn (fun z : ℝ × Vec =>
        ∑ k ∈ cutoffModes N, fourierCharacter k z.2 *
          galerkinRhs ν N (g.coeff z.1) k i) forwardSpacetime := by
      apply continuousOn_finset_sum
      intro k hk
      have hchar : Continuous (fun z : ℝ × Vec => fourierCharacter k z.2) :=
        (fourierCharacter_contDiff k).continuous.comp continuous_snd
      exact hchar.continuousOn.mul
        ((g.rhs_continuousOn hk i).comp continuous_fst.continuousOn
          (fun z hz => hz))
    have hre := Complex.continuous_re.comp_continuousOn hsum
    have hvec : ContinuousOn (fun _ : ℝ × Vec => unitVector i) forwardSpacetime :=
      continuousOn_const
    simpa only [Function.comp_def, Pi.smul_apply] using! hre.smul hvec
  apply hc.congr
  intro z hz
  exact congrFun (g.timeDerivative_eq_finiteSynthesis z.1 hz) z.2

theorem GalerkinSolution.timeDerivative_energy_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in unitCube, ‖timeDerivative g.velocity t x‖ ^ 2) =
      coefficientEnergy N (galerkinRhs ν N (g.coeff t)) := by
  rw [g.timeDerivative_eq_finiteSynthesis t ht,
    ← physicalEnergy_eq_integral_norm_sq]
  exact FINITE_PHYSICAL_ENERGY_PARSEVAL N _
    (galerkinRhs_reality ν N (g.coeff t) (g.real_symmetry t ht))

theorem GalerkinSolution.timeDerivative_energy_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t : ℝ => ∫ x in unitCube,
      ‖timeDerivative g.velocity t x‖ ^ 2) (Ici 0) := by
  have hc : ContinuousOn (fun t : ℝ =>
      coefficientEnergy N (galerkinRhs ν N (g.coeff t))) (Ici 0) := by
    unfold coefficientEnergy
    apply continuousOn_finset_sum
    intro k hk
    apply continuousOn_finset_sum
    intro i _
    simp_rw [Complex.normSq_eq_norm_sq]
    exact (g.rhs_continuousOn hk i).norm.pow 2
  apply hc.congr
  intro t ht
  exact g.timeDerivative_energy_eq t ht

theorem GalerkinSolution.timeDerivative_energy_intervalIntegrable
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => ∫ x in unitCube,
      ‖timeDerivative g.velocity t x‖ ^ 2) volume 0 T :=
  (g.timeDerivative_energy_continuousOn.mono
    (fun t ht => ht.1)).intervalIntegrable_of_Icc hT

theorem GALERKIN_TIME_DERIVATIVE_CUBIC_BOUND (ν : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Field) (N : ℕ) (g : GalerkinSolution ν a N)
      (t : ℝ), 0 ≤ t →
      (∫ x in unitCube, ‖timeDerivative g.velocity t x‖ ^ 2) ≤
        C * ((coefficientDissipation N (g.coeff t)) ^ 3 +
          coefficientLaplacianSquare N (g.coeff t)) := by
  obtain ⟨K, hK, hnonlinear⟩ := FINITE_CONVECTION_SQUARE_BOUND
  refine ⟨2 * ν ^ 2 + 2 * K, by positivity, ?_⟩
  intro a N g t ht
  have he := coefficientDissipation_nonneg N (g.coeff t)
  have hc := hnonlinear N (g.coeff t) (g.real_symmetry t ht)
  have hderiv := g.timeDerivative_L2_bound t ht
  change (∫ x in unitCube, ‖convection (g.velocity t) x‖ ^ 2) ≤ _ at hc
  have hprod : 0 ≤ ν ^ 2 * (coefficientDissipation N (g.coeff t)) ^ 3 :=
    mul_nonneg (sq_nonneg ν) (pow_nonneg he 3)
  nlinarith

/-- AX6 gives a cutoff-independent integral of the actual squared time derivative. -/
theorem AX6_UNIFORM_TIME_DERIVATIVE_BOUND (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) ≤ B := by
  obtain ⟨S, hS, hacc⟩ := AX6_UNIFORM_ENSTROPHY_ACCUMULATION hAX6 ν hν a ha T hT
  obtain ⟨C, hC, htime⟩ := GALERKIN_TIME_DERIVATIVE_CUBIC_BOUND ν
  refine ⟨C * (T * S ^ 3 + S / ν),
    mul_nonneg hC.le (add_nonneg (mul_nonneg hT.le (pow_nonneg hS 3))
      (div_nonneg hS hν.le)), ?_⟩
  intro N hN g
  have hZint : IntervalIntegrable (fun t : ℝ =>
      coefficientLaplacianSquare N (g.coeff t)) volume 0 T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => ht.1)).intervalIntegrable_of_Icc hT.le
  have hEn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      coefficientDissipation N (g.coeff t) ≤ S := by
    have h := hacc N hN g t ht
    have hz : 0 ≤ ∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s) :=
      intervalIntegral.integral_nonneg_of_forall ht.1
        (fun s => coefficientLaplacianSquare_nonneg N (g.coeff s))
    nlinarith [mul_nonneg hν.le hz]
  have hZ : (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t)) ≤ S / ν := by
    apply (le_div_iff₀ hν).2
    have h := hacc N hN g T ⟨hT.le, le_rfl⟩
    nlinarith [coefficientDissipation_nonneg N (g.coeff T)]
  have hboundInt : IntervalIntegrable (fun t : ℝ =>
      C * (S ^ 3 + coefficientLaplacianSquare N (g.coeff t))) volume 0 T :=
    (intervalIntegrable_const.add hZint).const_mul C
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, C * (S ^ 3 + coefficientLaplacianSquare N (g.coeff t)) := by
      apply intervalIntegral.integral_mono_on hT.le
        (g.timeDerivative_energy_intervalIntegrable hT.le) hboundInt
      intro t ht
      exact (htime a N g t ht.1).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (pow_le_pow_left₀
            (coefficientDissipation_nonneg N (g.coeff t)) (hEn t ht) 3) le_rfl) hC.le)
    _ = C * (T * S ^ 3 +
        ∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add intervalIntegrable_const hZint,
        intervalIntegral.integral_const]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hZ) hC.le

end

end SingularClosure
