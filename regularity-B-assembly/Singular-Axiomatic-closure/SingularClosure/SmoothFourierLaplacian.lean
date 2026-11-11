import SingularClosure.SobolevSmoothRealization
import SingularClosure.FiniteHessian
import SingularClosure.SmoothSixEnstrophy

/-! Exact physical Fourier identities for smooth periodic Laplacians. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem datumFourierCoeff_add (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a + b) = datumFourierCoeff a + datumFourierCoeff b := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [Pi.add_apply, PiLp.add_apply, Complex.ofReal_add, mul_add]
  exact integral_add (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_real_smul (z : ℝ) (a : Field) :
    datumFourierCoeff (z • a) = (z : ℂ) • datumFourierCoeff a := by
  funext k i
  have hpoint (x : Vec) : datumFourierIntegrand (z • a) k i x =
      (z : ℂ) * datumFourierIntegrand a k i x := by
    simp [datumFourierIntegrand, mul_comm, mul_left_comm, mul_assoc]
  change (∫ x in unitCube, datumFourierIntegrand (z • a) k i x) =
    (z : ℂ) * ∫ x in unitCube, datumFourierIntegrand a k i x
  simp_rw [hpoint]
  exact integral_const_mul _ _

theorem laplacian_contDiff (a : Field) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (laplacian a) := by
  change ContDiff ℝ ∞ (fun x => ∑ j : Fin 3,
    coordinateDerivative (coordinateDerivative a j) j x)
  apply contDiff_sum
  intro j _
  exact coordinateDerivative_smooth (coordinateDerivative_smooth ha j) j

theorem laplacian_spatialPeriodic (a : Field) (hp : SpatialPeriodic a) :
    SpatialPeriodic (laplacian a) := by
  intro x i
  unfold laplacian
  apply Finset.sum_congr rfl
  intro j _
  exact coordinateDerivative_spatialPeriodic j (coordinateDerivative a j)
    (coordinateDerivative_spatialPeriodic j a hp) x i

theorem datumFourierCoeff_laplacian (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    datumFourierCoeff (laplacian a) = laplacianCoefficient (datumFourierCoeff a) := by
  funext k i
  have hpoint (x : Vec) : datumFourierIntegrand (laplacian a) k i x =
      ∑ j : Fin 3,
        datumFourierIntegrand (coordinateDerivative (coordinateDerivative a j) j) k i x := by
    have hproj := map_sum (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)
      (fun j : Fin 3 => coordinateDerivative (coordinateDerivative a j) j x) Finset.univ
    have hi : laplacian a x i =
        ∑ j : Fin 3, coordinateDerivative (coordinateDerivative a j) j x i := by
      simpa only [laplacian, coordinateDerivative, EuclideanSpace.coe_proj] using hproj
    simp only [datumFourierIntegrand, hi, Complex.ofReal_sum, Finset.mul_sum]
  change (∫ x in unitCube, datumFourierIntegrand (laplacian a) k i x) = _
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ
    (f := fun j x => datumFourierIntegrand
      (coordinateDerivative (coordinateDerivative a j) j) k i x)
    (fun j _ => datumFourierIntegrand_integrableOn
      (coordinateDerivative_smooth (coordinateDerivative_smooth ha j) j).continuous k i)]
  change (∑ j : Fin 3,
    datumFourierCoeff (coordinateDerivative (coordinateDerivative a j) j) k i) = _
  have hD (j : Fin 3) :
      datumFourierCoeff (coordinateDerivative (coordinateDerivative a j) j) =
        spectralMultiplier (derivativeSymbol j)
          (spectralMultiplier (derivativeSymbol j) (datumFourierCoeff a)) := by
    rw [datumFourierCoeff_coordinateDerivative j (coordinateDerivative a j)
      (coordinateDerivative_smooth ha j) (coordinateDerivative_spatialPeriodic j a hp),
      datumFourierCoeff_coordinateDerivative j a ha hp]
  simp_rw [hD]
  exact congrArg (fun c : FourierCoeff => c k i)
    (sum_double_derivativeMultiplier (datumFourierCoeff a))

theorem smoothFourierSynthesis_laplacian_coeff (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) :
    datumFourierCoeff (laplacian (smoothFourierSynthesis c)) = laplacianCoefficient c := by
  rw [datumFourierCoeff_laplacian _ (smoothFourierSynthesis_contDiff c hc)
    (smoothFourierSynthesis_periodic c), datumFourierCoeff_smoothFourierSynthesis c hc hreal]

end

end SingularClosure
