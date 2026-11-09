import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

noncomputable section

open Set Algebra Submodule MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace CEATheta

open UnitAddTorus

abbrev TorusL2 (d : Type*) [Fintype d] :=
  MeasureTheory.Lp ℂ 2 (volume : Measure (UnitAddTorus d))

theorem torus_scalar_finite_parseval
    {d : Type*} [Fintype d]
    (f : TorusL2 d)
    (s : Finset (d → ℤ))
    (hzero : ∀ k, k ∉ s → mFourierCoeff f k = 0) :
    Finset.sum s (fun k => ‖mFourierCoeff f k‖ ^ 2)
      =
    ∫ t, ‖f t‖ ^ 2 := by
  have hparseval :
      (∑' k : d → ℤ, ‖mFourierCoeff f k‖ ^ 2)
        =
      ∫ t, ‖f t‖ ^ 2 :=
    (hasSum_sq_mFourierCoeff f).tsum_eq
  rw [tsum_eq_sum (s := s) (fun k hk => by
    simp [hzero k hk])] at hparseval
  exact hparseval

abbrev Torus3ScalarL2 := TorusL2 (Fin 3)
abbrev Torus3VectorL2 := Fin 3 → Torus3ScalarL2

noncomputable def torus3VectorL2Sq (u : Torus3VectorL2) : ℝ :=
  Finset.sum Finset.univ (fun c : Fin 3 => ∫ t, ‖u c t‖ ^ 2)

noncomputable def torus3VectorFourierSq
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ)) : ℝ :=
  Finset.sum Finset.univ (fun c : Fin 3 =>
    Finset.sum s (fun k => ‖mFourierCoeff (u c) k‖ ^ 2))

theorem torus3_vector_finite_parseval
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ))
    (hzero :
      ∀ c : Fin 3, ∀ k, k ∉ s → mFourierCoeff (u c) k = 0) :
    torus3VectorFourierSq u s = torus3VectorL2Sq u := by
  unfold torus3VectorFourierSq torus3VectorL2Sq
  apply Finset.sum_congr rfl
  intro c hc
  exact torus_scalar_finite_parseval (u c) s (hzero c)

theorem torus3_l2_dictionary_field
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ))
    (hzero :
      ∀ c : Fin 3, ∀ k, k ∉ s → mFourierCoeff (u c) k = 0) :
    torus3VectorL2Sq u =
      Finset.sum Finset.univ (fun c : Fin 3 =>
        Finset.sum s (fun k => ‖mFourierCoeff (u c) k‖ ^ 2)) := by
  symm
  exact torus3_vector_finite_parseval u s hzero

#print axioms CEATheta.torus_scalar_finite_parseval
#print axioms CEATheta.torus3_vector_finite_parseval
#print axioms CEATheta.torus3_l2_dictionary_field

end CEATheta
