import SingularClosure.ComplexCoordinateAverage
import SingularClosure.SmoothSixChannels

/-! Identification of literal physical averages with the finite Fourier masks. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def coordinateCoefficientAverage (j : Fin 3) (c : FourierCoeff) : FourierCoeff :=
  fun k i => if k j = 0 then c k i else 0

def verticalCoefficient (c : FourierCoeff) : FourierCoeff :=
  fun k i => if i = 2 then c k i else 0

theorem finiteSynthesis_sub (N : ℕ) (a b : FourierCoeff) :
    finiteSynthesis N (a - b) = finiteSynthesis N a - finiteSynthesis N b := by
  funext x
  ext i
  simp [finiteSynthesis, mul_sub, Finset.sum_sub_distrib]

theorem coordinateAverage_finiteSynthesis (j : Fin 3) (N : ℕ) (c : FourierCoeff) :
    coordinateAverage j (finiteSynthesis N c) =
      finiteSynthesis N (coordinateCoefficientAverage j c) := by
  funext x
  ext i
  have hc (k : Frequency) : Continuous (fun s : ℝ =>
      fourierCharacter k (resetCoordinate j s x) * c k i) :=
    ((fourierCharacter_contDiff k).continuous.comp
      (resetCoordinate_continuous_slice j x)).mul continuous_const
  have hsum : IntegrableOn (fun s : ℝ =>
      ∑ k ∈ cutoffModes N, fourierCharacter k (resetCoordinate j s x) * c k i)
      (Icc (0 : ℝ) 1) volume :=
    (continuous_finsetSum _ (fun k _ => hc k)).continuousOn.integrableOn_compact isCompact_Icc
  have hchar (k : Frequency) :
      (∫ s in Icc (0 : ℝ) 1, fourierCharacter k (resetCoordinate j s x)) =
        if k j = 0 then fourierCharacter k x else 0 := by
    exact congrFun (complexCoordinateAverage_fourierCharacter j k) x
  rw [coordinateAverage_component j (finiteSynthesis N c)
    (finiteSynthesis_contDiff N c).continuous x i]
  change (∫ s in Icc (0 : ℝ) 1,
    (∑ k ∈ cutoffModes N, fourierCharacter k (resetCoordinate j s x) * c k i).re) =
    (∑ k ∈ cutoffModes N, fourierCharacter k x * coordinateCoefficientAverage j c k i).re
  calc
    _ = (∫ s in Icc (0 : ℝ) 1,
        ∑ k ∈ cutoffModes N, fourierCharacter k (resetCoordinate j s x) * c k i).re :=
      Complex.reCLM.integral_comp_comm hsum
    _ = (∑ k ∈ cutoffModes N,
        (∫ s in Icc (0 : ℝ) 1, fourierCharacter k (resetCoordinate j s x)) * c k i).re := by
      congr 1
      rw [integral_finsetSum (cutoffModes N)
        (f := fun k s => fourierCharacter k (resetCoordinate j s x) * c k i)
        (μ := volume.restrict (Icc (0 : ℝ) 1))
        (fun k _ => (hc k).continuousOn.integrableOn_compact isCompact_Icc)]
      simp_rw [integral_mul_const]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [hchar]
      by_cases hk : k j = 0 <;> simp [coordinateCoefficientAverage, hk]

theorem verticalComponent_finiteSynthesis (N : ℕ) (c : FourierCoeff) :
    verticalComponent (finiteSynthesis N c) = finiteSynthesis N (verticalCoefficient c) := by
  funext x
  ext i
  by_cases hi : i = 2
  · subst i
    simp [verticalComponent, verticalComponentCLM, unitVector, finiteSynthesis,
      verticalCoefficient]
  · simp [verticalComponent, verticalComponentCLM, unitVector, finiteSynthesis,
      verticalCoefficient, hi]

def synthesizedBaseV (c : FourierCoeff) : FourierCoeff :=
  coordinateCoefficientAverage 2 c - verticalCoefficient (coordinateCoefficientAverage 2 c)

def synthesizedBaseW (c : FourierCoeff) : FourierCoeff :=
  verticalCoefficient (coordinateCoefficientAverage 2 c)

def synthesizedBaseR (c : FourierCoeff) : FourierCoeff := c - coordinateCoefficientAverage 2 c

def synthesizedSixCoefficient (A : Fin 6) (c : FourierCoeff) : FourierCoeff :=
  ![coordinateCoefficientAverage 0 (synthesizedBaseV c),
    synthesizedBaseV c - coordinateCoefficientAverage 0 (synthesizedBaseV c),
    coordinateCoefficientAverage 0 (synthesizedBaseW c),
    synthesizedBaseW c - coordinateCoefficientAverage 0 (synthesizedBaseW c),
    coordinateCoefficientAverage 0 (synthesizedBaseR c),
    synthesizedBaseR c - coordinateCoefficientAverage 0 (synthesizedBaseR c)] A

theorem smoothSixChannel_synthesized_coefficient (A : Fin 6) (N : ℕ) (c : FourierCoeff) :
    smoothSixChannel A (finiteSynthesis N c) =
      finiteSynthesis N (synthesizedSixCoefficient A c) := by
  fin_cases A <;>
    simp [smoothSixChannel, synthesizedSixCoefficient, baseChannelV, baseChannelW,
      baseChannelR, synthesizedBaseV, synthesizedBaseW, synthesizedBaseR,
      coordinateAverage_finiteSynthesis, verticalComponent_finiteSynthesis,
      ← finiteSynthesis_sub]

theorem synthesizedSixCoefficient_eq_spectralChannel (A : Fin 6) (c : FourierCoeff) :
    synthesizedSixCoefficient A c = spectralChannel A c := by
  funext k i
  fin_cases A <;>
    by_cases h0 : k 0 = 0 <;> by_cases h2 : k 2 = 0 <;> by_cases hi : i = 2 <;>
      simp [synthesizedSixCoefficient, synthesizedBaseV, synthesizedBaseW, synthesizedBaseR,
        coordinateCoefficientAverage, verticalCoefficient, spectralChannel, channelOf, h0, h2, hi]

/-- Exact identification of the complete physical coordinate-average channels
with the finite coefficient masks used by the actual Galerkin system. -/
theorem smoothSixChannel_finiteSynthesis (A : Fin 6) (N : ℕ) (c : FourierCoeff) :
    smoothSixChannel A (finiteSynthesis N c) =
      finiteSynthesis N (spectralChannel A c) := by
  rw [smoothSixChannel_synthesized_coefficient, synthesizedSixCoefficient_eq_spectralChannel]

end

end SingularClosure
