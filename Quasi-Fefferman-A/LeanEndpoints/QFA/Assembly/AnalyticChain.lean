import QFA.Assembly.AnalyticInputs
import QFA.Assembly.Representation
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# QFA assembly: compact derivative data to nonlinear absorption

Status: A_TIER_CANDIDATE. No local Lean or Lake execution.
External baseline: Lean 4.33.0 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
Local declarations: LE094--LE097. New source entrypoint: EP140.

The spectral contract already contains all three moment integrability
statements. Their nonnegative quadratic moment gives interpolation without
an additional moment, measurability, or positivity assumption. In particular,
LC001 implies LC002, while no unconditional inhabitant of either is supplied.

The remaining assembly starts from actual real spatial L2 fields with supplied
compact-test first/diagonal-second derivatives and an actual Laplacian sum.
LC004, LC001, and LC003 remain explicit analytic premises. The nonlinear value
N, derivative value d, convection estimate, and enstrophy inequality remain
supplied inputs. The output is pointwise in the field data: no temporal
invariant, derivative existence, strong solution, or QFA root is concluded.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction FourierTransform

namespace QFA.Assembly.AnalyticChain

open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation
open QFA.Assembly.Representation
open QFA.Assembly.AnalyticInputs

noncomputable section

/-- The three genuine spectral moments imply interpolation, including all
zero-energy cases. Nonnegativity of the integrated square gives a quadratic
with nonpositive discriminant. No division by a field energy is used.
-/
theorem interpolation_of_nativeSpectralRealization
    {v L : ComplexL2} {G : Fin 3 → ComplexL2}
    (hSpectral : NativeSpectralRealization v G L) :
    gradientEnergy G ^ 2 ≤ velocityEnergy v * laplacianEnergy L := by
  let q : Space → ℝ := fun k => ‖(𝓕 v : ComplexL2) k‖ ^ 2
  let w : Space → ℝ := fun k => (2 * Real.pi) ^ 2 * ‖k‖ ^ 2
  have hq : Integrable q volume := hSpectral.energy_integrable
  have hwq : Integrable (fun k : Space => w k * q k) volume :=
    hSpectral.gradient_integrable
  have hWeight (k : Space) : w k ^ 2 * q k =
      (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * ‖(𝓕 v : ComplexL2) k‖ ^ 2 := by
    dsimp [w, q]
    ring
  have hw2q : Integrable (fun k : Space => w k ^ 2 * q k) volume := by
    simp_rw [hWeight]
    exact hSpectral.laplacian_integrable
  have hE : velocityEnergy v = ∫ k : Space, q k := hSpectral.energy_identity
  have hD : gradientEnergy G = ∫ k : Space, w k * q k := hSpectral.gradient_identity
  have hZ : laplacianEnergy L = ∫ k : Space, w k ^ 2 * q k := by
    simp_rw [hWeight]
    exact hSpectral.laplacian_identity
  have hPolynomial : ∀ x : ℝ,
      0 ≤ velocityEnergy v * (x * x) + (-2 * gradientEnergy G) * x +
        laplacianEnergy L := by
    intro x
    have h0x : Integrable (fun k : Space => (x * x) * q k) volume :=
      hq.const_mul (x * x)
    have h1x : Integrable (fun k : Space => (2 * x) * (w k * q k)) volume :=
      hwq.const_mul (2 * x)
    have hIdentity : (∫ k : Space, (x - w k) ^ 2 * q k) =
        velocityEnergy v * (x * x) + (-2 * gradientEnergy G) * x +
          laplacianEnergy L := by
      calc
        (∫ k : Space, (x - w k) ^ 2 * q k) =
            ∫ k : Space, ((x * x) * q k - (2 * x) * (w k * q k)) +
              w k ^ 2 * q k := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun k => by ring)
        _ = ((x * x) * (∫ k : Space, q k) -
              (2 * x) * (∫ k : Space, w k * q k)) +
              (∫ k : Space, w k ^ 2 * q k) := by
          rw [integral_add (h0x.sub h1x) hw2q, integral_sub h0x h1x,
            integral_const_mul, integral_const_mul]
        _ = velocityEnergy v * (x * x) + (-2 * gradientEnergy G) * x +
              laplacianEnergy L := by
          rw [← hE, ← hD, ← hZ]
          ring
    rw [← hIdentity]
    apply integral_nonneg
    intro k
    exact mul_nonneg (sq_nonneg (x - w k)) (sq_nonneg ‖(𝓕 v : ComplexL2) k‖)
  have hDiscriminant :
      discrim (velocityEnergy v) (-2 * gradientEnergy G) (laplacianEnergy L) ≤ 0 :=
    -- EP140: an everywhere nonnegative real quadratic has nonpositive discriminant.
    discrim_le_zero hPolynomial
  dsimp [discrim] at hDiscriminant
  nlinarith only [hDiscriminant]

/-- Conditional construction of LC002 from LC001. The spectral endpoint
remains a premise; this is not an unconditional proof of either target.
-/
theorem interpolationEndpoint_of_spectralEndpoint
    (hSpectral : WholeSpaceSpectralEndpoint) : WholeSpaceInterpolationEndpoint := by
  intro v G L hDerivatives
  exact interpolation_of_nativeSpectralRealization (hSpectral v G L hDerivatives)

/-- Real compact-test derivative data are transported to Schwartz and spectral
witnesses, an actual a.e. bounded continuous representative, and a scalar
profile in the original real L2 energies. LC002 is derived from LC001.
-/
theorem exists_profile_of_compactData
    (hExtension : CompactToSchwartzEndpoint)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint)
    {v L : RealL2} {G H : Fin 3 → RealL2} {N : ℝ}
    (hDerivatives : CompactDerivativeData v G H L)
    (hN : 0 ≤ N)
    (hConvection : ∀ V : Space →ᵇ ComplexVector,
      (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) →
        N ≤ ‖V‖ * Real.sqrt (∑ j : Fin 3, ‖G j‖ ^ 2) * Real.sqrt (‖L‖ ^ 2)) :
    SchwartzDerivativeWitnesses (complexifyL2 v)
        (fun j => complexifyL2 (G j)) (complexifyL2 L) ∧
      NativeSpectralRealization (complexifyL2 v)
        (fun j => complexifyL2 (G j)) (complexifyL2 L) ∧
      ∃ V : Space →ᵇ ComplexVector,
        (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) ∧
          ScalarProfile (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) (‖L‖ ^ 2) ‖V‖ N := by
  have hSchwartz := schwartzWitnesses_of_compactData hExtension hDerivatives
  obtain ⟨V, hV, hProfile⟩ := exists_scalarProfile_of_analytic_endpoints
    (interpolationEndpoint_of_spectralEndpoint hSpectral) hAgmon hSchwartz hN
    (by
      intro V hV
      simpa only [complexifyL2_gradientEnergy, complexifyL2_laplacianEnergy]
        using hConvection V hV)
  refine ⟨hSchwartz, hSpectral _ _ _ hSchwartz, V, hV, ?_⟩
  simpa only [complexifyL2_velocityEnergy, complexifyL2_gradientEnergy,
    complexifyL2_laplacianEnergy] using hProfile

/-- Complete pointwise analytic chain from the supplied real derivative data
to the exact nonlinear fourth-power estimate and an explicit positive margin.

The field data and all unresolved analytic/physical premises are retained.
The number d is not identified here with a temporal enstrophy derivative.
-/
theorem exists_absorption_of_compactData
    (hExtension : CompactToSchwartzEndpoint)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint)
    {v L : RealL2} {G H : Fin 3 → RealL2} {N d ν : ℝ}
    (hDerivatives : CompactDerivativeData v G H L)
    (hN : 0 ≤ N)
    (hConvection : ∀ V : Space →ᵇ ComplexVector,
      (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) →
        N ≤ ‖V‖ * Real.sqrt (∑ j : Fin 3, ‖G j‖ ^ 2) * Real.sqrt (‖L‖ ^ 2))
    (hν : 0 < ν)
    (hSmall : (‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2) < 4 * Real.pi ^ 2 * ν ^ 4)
    (hEnstrophy : d / 2 + ν * ‖L‖ ^ 2 ≤ N) :
    SchwartzDerivativeWitnesses (complexifyL2 v)
        (fun j => complexifyL2 (G j)) (complexifyL2 L) ∧
      NativeSpectralRealization (complexifyL2 v)
        (fun j => complexifyL2 (G j)) (complexifyL2 L) ∧
      ∃ (V : Space →ᵇ ComplexVector) (η : ℝ),
        (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) ∧
        ScalarProfile (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) (‖L‖ ^ 2) ‖V‖ N ∧
        η = ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) ∧
        0 < η ∧
        4 * Real.pi ^ 2 * N ^ 4 ≤
          ((‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2)) * (‖L‖ ^ 2) ^ 4 ∧
        N ≤ (ν - η) * ‖L‖ ^ 2 ∧
        d + 2 * η * ‖L‖ ^ 2 ≤ 0 := by
  obtain ⟨hSchwartz, hRealization, V, hV, hProfile⟩ :=
    exists_profile_of_compactData hExtension hSpectral hAgmon hDerivatives hN hConvection
  refine ⟨hSchwartz, hRealization, V,
    ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2), hV, hProfile,
    rfl, hProfile.viscosity_margin_pos hν hSmall, hProfile.nonlinear_fourth_power,
    ?_, hProfile.enstrophy_absorption hEnstrophy⟩
  have hCoefficient : ν -
      (ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2)) =
      nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) := by ring
  simpa only [hCoefficient] using hProfile.nonlinear_le_coefficient

end

end QFA.Assembly.AnalyticChain
