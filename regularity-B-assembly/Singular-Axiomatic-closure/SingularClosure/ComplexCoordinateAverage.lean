import SingularClosure.CoordinateAverageOrthogonal
import SingularClosure.CoordinateAverageCalculus
import SingularClosure.FourierIntegral

/-! Complex scalar averages used to identify the literal physical Fourier masks. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def complexCoordinateAverage (j : Fin 3) (f : Vec → ℂ) : Vec → ℂ :=
  fun x => ∫ s in Icc (0 : ℝ) 1, f (resetCoordinate j s x)

theorem complexCoordinateAverage_continuous (j : Fin 3) (f : Vec → ℂ)
    (hf : Continuous f) : Continuous (complexCoordinateAverage j f) := by
  apply continuous_parametric_integral_of_continuous
    (f := fun x s => f (resetCoordinate j s x)) ?_ isCompact_Icc
  exact hf.comp (resetCoordinate_smooth j).continuous

theorem complexCoordinateAverage_insertNth (j : Fin 3) (f : Vec → ℂ)
    (s t : ℝ) (y : Fin 2 → ℝ) :
    complexCoordinateAverage j f (WithLp.toLp 2 (j.insertNth s y)) =
      complexCoordinateAverage j f (WithLp.toLp 2 (j.insertNth t y)) := by
  simp only [complexCoordinateAverage, resetCoordinate_insertNth]

theorem complexCoordinateAverage_selfAdjoint_mul (j : Fin 3) (f g : Vec → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in unitCube, complexCoordinateAverage j f x * g x) =
      ∫ x in unitCube, f x * complexCoordinateAverage j g x := by
  rw [integral_unitCube_disintegrate j
      (fun x => complexCoordinateAverage j f x * g x)
      ((complexCoordinateAverage_continuous j f hf).mul hg),
    integral_unitCube_disintegrate j
      (fun x => f x * complexCoordinateAverage j g x)
      (hf.mul (complexCoordinateAverage_continuous j g hg))]
  apply integral_congr_ae
  filter_upwards with y
  let x : Vec := WithLp.toLp 2 (j.insertNth 0 y)
  have hfavg : (∫ s in Icc (0 : ℝ) 1,
      f (WithLp.toLp 2 (j.insertNth s y))) = complexCoordinateAverage j f x := by
    simp only [complexCoordinateAverage, x, resetCoordinate_insertNth]
  have hgavg : (∫ s in Icc (0 : ℝ) 1,
      g (WithLp.toLp 2 (j.insertNth s y))) = complexCoordinateAverage j g x := by
    simp only [complexCoordinateAverage, x, resetCoordinate_insertNth]
  simp_rw [complexCoordinateAverage_insertNth j f _ 0 y,
    complexCoordinateAverage_insertNth j g _ 0 y]
  change (∫ s in Icc (0 : ℝ) 1,
      complexCoordinateAverage j f x * g (WithLp.toLp 2 (j.insertNth s y))) =
    ∫ s in Icc (0 : ℝ) 1,
      f (WithLp.toLp 2 (j.insertNth s y)) * complexCoordinateAverage j g x
  rw [integral_const_mul, integral_mul_const, hfavg, hgavg]

/-- Exact character eigenvalues of a literal coordinate integral. -/
theorem complexCoordinateAverage_fourierCharacter (j : Fin 3) (k : Frequency) :
    complexCoordinateAverage j (fourierCharacter k) =
      fun x => if k j = 0 then fourierCharacter k x else 0 := by
  have hprod (y : Vec) : fourierCharacter k y =
      fourier (k 0) (y 0 : UnitAddCircle) *
        fourier (k 1) (y 1 : UnitAddCircle) * fourier (k 2) (y 2 : UnitAddCircle) := by
    rw [fourierCharacter_eq_product, Fin.prod_univ_three]
  funext x
  fin_cases j
  · change (∫ s in Icc (0 : ℝ) 1, fourierCharacter k (resetCoordinate 0 s x)) =
      if k 0 = 0 then fourierCharacter k x else 0
    simp_rw [hprod]
    change (∫ s in Icc (0 : ℝ) 1,
      fourier (k 0) (s : UnitAddCircle) * fourier (k 1) (x 1 : UnitAddCircle) *
        fourier (k 2) (x 2 : UnitAddCircle)) = _
    rw [integral_mul_const, integral_mul_const, integral_oneDimensional_character]
    by_cases hk : k 0 = 0 <;> simp [hk]
  · change (∫ s in Icc (0 : ℝ) 1, fourierCharacter k (resetCoordinate 1 s x)) =
      if k 1 = 0 then fourierCharacter k x else 0
    simp_rw [hprod]
    change (∫ s in Icc (0 : ℝ) 1,
      fourier (k 0) (x 0 : UnitAddCircle) * fourier (k 1) (s : UnitAddCircle) *
        fourier (k 2) (x 2 : UnitAddCircle)) = _
    rw [integral_mul_const, integral_const_mul, integral_oneDimensional_character]
    by_cases hk : k 1 = 0 <;> simp [hk]
  · change (∫ s in Icc (0 : ℝ) 1, fourierCharacter k (resetCoordinate 2 s x)) =
      if k 2 = 0 then fourierCharacter k x else 0
    simp_rw [hprod]
    change (∫ s in Icc (0 : ℝ) 1,
      fourier (k 0) (x 0 : UnitAddCircle) * fourier (k 1) (x 1 : UnitAddCircle) *
        fourier (k 2) (s : UnitAddCircle)) = _
    rw [integral_const_mul, integral_oneDimensional_character]
    by_cases hk : k 2 = 0 <;> simp [hk]

theorem complexCoordinateAverage_star_character (j : Fin 3) (k : Frequency) :
    complexCoordinateAverage j (fun x => star (fourierCharacter k x)) =
      fun x => if k j = 0 then star (fourierCharacter k x) else 0 := by
  have he : (fun x => star (fourierCharacter k x)) = fourierCharacter (-k) := by
    funext x
    exact (fourierCharacter_neg k x).symm
  rw [he, complexCoordinateAverage_fourierCharacter]
  funext x
  simp [fourierCharacter_neg]

theorem complexCoordinateAverage_component (j : Fin 3) (a : Field)
    (ha : Continuous a) (i : Fin 3) :
    complexCoordinateAverage j (fun x => (a x i : ℂ)) =
      fun x => (coordinateAverage j a x i : ℂ) := by
  funext x
  rw [coordinateAverage_component j a ha]
  exact integral_complex_ofReal

end

end SingularClosure
