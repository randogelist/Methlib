import SingularClosure.ComplexCoordinateAverage
import SingularClosure.SmoothSixProjectionAlgebra
import SingularClosure.InitialFourier

/-!
# Exact Fourier coefficients of the six physical channels

The left sides are the actual cube integrals of the physical coordinate
averages. The identities establish their equality with the fixed coefficient
masks, rather than assuming a Fourier representation of the input field.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem datumFourierCoeff_coordinateAverage (j : Fin 3) (a : Field)
    (ha : Continuous a) :
    datumFourierCoeff (coordinateAverage j a) =
      fun k i => if k j = 0 then datumFourierCoeff a k i else 0 := by
  funext k i
  have hs := complexCoordinateAverage_selfAdjoint_mul j
    (fun x => star (fourierCharacter k x)) (fun x => (a x i : ℂ))
    (fourierCharacter_contDiff k).continuous.star
    (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha))
  rw [complexCoordinateAverage_star_character,
    complexCoordinateAverage_component j a ha i] at hs
  by_cases hk : k j = 0
  · simpa [datumFourierCoeff, datumFourierIntegrand, hk] using hs.symm
  · simpa [datumFourierCoeff, datumFourierIntegrand, hk] using hs.symm

theorem datumFourierCoeff_sub (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [Pi.sub_apply, PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  exact integral_sub (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

theorem datumFourierCoeff_verticalComponent (a : Field) :
    datumFourierCoeff (verticalComponent a) =
      fun k i => if i = 2 then datumFourierCoeff a k i else 0 := by
  funext k i
  by_cases hi : i = 2
  · subst i
    simp [datumFourierCoeff, datumFourierIntegrand,
      verticalComponent, verticalComponentCLM, unitVector]
  · simp [datumFourierCoeff, datumFourierIntegrand,
      verticalComponent, verticalComponentCLM, unitVector, hi, Ne.symm hi]

set_option maxHeartbeats 1000000 in
/-- Identification of every literal smooth channel with its frozen Fourier mask. -/
theorem datumFourierCoeff_smoothSixChannel (A : Fin 6) (a : Field)
    (ha : Continuous a) :
    datumFourierCoeff (smoothSixChannel A a) = spectralChannel A (datumFourierCoeff a) := by
  have hsub (u v : Field) (hu : Continuous u) (hv : Continuous v) : Continuous (u - v) := by
    change Continuous (fun x => u x - v x)
    exact hu.sub hv
  fin_cases A <;> funext k i <;>
    by_cases h2 : k 2 = 0 <;> by_cases h0 : k 0 = 0 <;> by_cases hi : i = 2 <;>
      simp (disch := solve_by_elim (maxDepth := 32)
        [coordinateAverage_continuous, verticalComponent_continuous, hsub])
        [smoothSixChannel, baseChannelV, baseChannelW, baseChannelR,
          datumFourierCoeff_sub, datumFourierCoeff_coordinateAverage,
          datumFourierCoeff_verticalComponent, spectralChannel, channelOf, h2, h0, hi]

end

end SingularClosure
