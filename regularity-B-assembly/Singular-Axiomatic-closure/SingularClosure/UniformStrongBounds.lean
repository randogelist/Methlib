import SingularClosure.StrongTimeBounds
import SingularClosure.PhysicalEnergy

/-!
# Uniform physical strong bounds from the single AX6 premise

The quantities are actual physical L2, gradient and Laplacian integrals.
The H2 square uses the standard Fourier weight (1+|2 pi k|^2)^2.
All finite-time integrability claims are proved for the actual trajectory.
No strong-limit, compactness, or smoothing premise occurs here.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

def physicalH1Square (v : Field) : ℝ := physicalEnergy v + physicalDissipation v

def physicalH2Square (v : Field) : ℝ :=
  physicalEnergy v + 2 * physicalDissipation v +
    ∫ x in unitCube, ‖laplacian v x‖ ^ 2

theorem GalerkinSolution.physicalH1Square_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    physicalH1Square (g.velocity t) =
      coefficientEnergy N (g.coeff t) + coefficientDissipation N (g.coeff t) := by
  rw [physicalH1Square, g.physicalEnergy_eq ht, g.physicalDissipation_eq ht]

theorem GalerkinSolution.physicalH2Square_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    physicalH2Square (g.velocity t) =
      coefficientEnergy N (g.coeff t) + 2 * coefficientDissipation N (g.coeff t) +
        coefficientLaplacianSquare N (g.coeff t) := by
  rw [physicalH2Square, g.physicalEnergy_eq ht, g.physicalDissipation_eq ht]
  exact congrArg (fun z => coefficientEnergy N (g.coeff t) +
    2 * coefficientDissipation N (g.coeff t) + z)
    (finite_laplacian_integral_norm_sq N (g.coeff t) (g.real_symmetry t ht))

theorem GalerkinSolution.physicalH1Square_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => physicalH1Square (g.velocity t)) (Ici 0) := by
  apply (g.coefficientEnergy_continuousOn.add
    g.coefficientDissipation_continuousOn).congr
  intro t ht
  exact g.physicalH1Square_eq ht

theorem GalerkinSolution.physicalH2Square_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => physicalH2Square (g.velocity t)) (Ici 0) := by
  apply ((g.coefficientEnergy_continuousOn.add
    (continuousOn_const.mul g.coefficientDissipation_continuousOn)).add
    g.coefficientLaplacianSquare_continuousOn).congr
  intro t ht
  exact g.physicalH2Square_eq ht

/-- Uniform actual H1, H2 and time-derivative square bounds. The same B works
for every positive cutoff and every actual Galerkin trajectory. -/
theorem AX6_UNIFORM_PHYSICAL_STRONG_BOUNDS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∀ t ∈ Icc (0 : ℝ) T, physicalH1Square (g.velocity t) ≤ B) ∧
      IntervalIntegrable (fun t => physicalH2Square (g.velocity t)) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, physicalH2Square (g.velocity t)) ≤ B ∧
      IntervalIntegrable (fun t => ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) ≤ B := by
  obtain ⟨S, hS, hacc⟩ := AX6_UNIFORM_ENSTROPHY_ACCUMULATION hAX6 ν hν a ha T hT
  obtain ⟨D, hD, htime⟩ := AX6_UNIFORM_TIME_DERIVATIVE_BOUND hAX6 ν hν a ha T hT
  let J : ℝ := physicalEnergy a
  have hJ : 0 ≤ J := by
    change 0 ≤ physicalEnergy a
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg _)
  let B : ℝ := (J + 2 * S) * (T + 1) + S / ν + D
  have hJ2 : 0 ≤ J + 2 * S := by positivity
  have hdiv : 0 ≤ S / ν := div_nonneg hS hν.le
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro N hN g
  have hE (t : ℝ) (ht : 0 ≤ t) : coefficientEnergy N (g.coeff t) ≤ J := by
    calc
      _ ≤ coefficientEnergy N (g.coeff 0) := g.coefficientEnergy_le_initial hν.le ht
      _ = coefficientEnergy N (datumFourierCoeff a) := g.coefficientEnergy_initial_eq
      _ ≤ J := coefficientEnergy_initial_cutoff_le N a ha.smooth.continuous
  have hEn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      coefficientDissipation N (g.coeff t) ≤ S := by
    have hh := hacc N hN g t ht
    have hz : 0 ≤ ∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s) :=
      intervalIntegral.integral_nonneg_of_forall ht.1
        (fun s => coefficientLaplacianSquare_nonneg N (g.coeff s))
    nlinarith [mul_nonneg hν.le hz]
  have hZi : IntervalIntegrable (fun t => coefficientLaplacianSquare N (g.coeff t))
      volume 0 T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => ht.1)).intervalIntegrable_of_Icc hT.le
  have hZ : (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t)) ≤ S / ν := by
    apply (le_div_iff₀ hν).2
    have hh := hacc N hN g T ⟨hT.le, le_rfl⟩
    nlinarith [coefficientDissipation_nonneg N (g.coeff T)]
  have hH2 : IntervalIntegrable (fun t => physicalH2Square (g.velocity t)) volume 0 T :=
    (g.physicalH2Square_continuousOn.mono
      (fun t ht => ht.1)).intervalIntegrable_of_Icc hT.le
  refine ⟨?_, hH2, ?_, g.timeDerivative_energy_intervalIntegrable hT.le, ?_⟩
  · intro t ht
    rw [g.physicalH1Square_eq ht.1]
    have h1 := hE t ht.1
    have h2 := hEn t ht
    dsimp [B]
    nlinarith [mul_nonneg hJ2 hT.le]
  · have hbound : (∫ t in (0 : ℝ)..T, physicalH2Square (g.velocity t)) ≤
        T * (J + 2 * S) + S / ν := by
      calc
        _ ≤ ∫ t in (0 : ℝ)..T,
            (J + 2 * S) + coefficientLaplacianSquare N (g.coeff t) := by
          apply intervalIntegral.integral_mono_on hT.le hH2
            (intervalIntegrable_const.add hZi)
          intro t ht
          rw [g.physicalH2Square_eq ht.1]
          have h1 := hE t ht.1
          have h2 := hEn t ht
          linarith
        _ = T * (J + 2 * S) +
            ∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
            intervalIntegral.integral_const]
          simp
        _ ≤ _ := add_le_add_left hZ _
    dsimp [B]
    nlinarith
  · have hh := htime N hN g
    dsimp [B]
    nlinarith [mul_nonneg hJ2 (show 0 ≤ T + 1 by linarith)]

end

end SingularClosure
