import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Ring

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

abbrev Torus3ScalarL2 := TorusL2 (Fin 3)
abbrev Torus3VectorL2 := Fin 3 → Torus3ScalarL2

def torus3ModeSq (k : (Fin 3) → ℤ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin 3 => ((k i : ℝ) ^ 2))

noncomputable def torus3StokesEigenvalue (k : (Fin 3) → ℤ) : ℝ :=
  (2 * Real.pi) ^ 2 * torus3ModeSq k

theorem torus3ModeSq_nonneg (k : (Fin 3) → ℤ) :
    0 ≤ torus3ModeSq k := by
  unfold torus3ModeSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (k i : ℝ))

theorem torus3StokesEigenvalue_nonneg (k : (Fin 3) → ℤ) :
    0 ≤ torus3StokesEigenvalue k := by
  unfold torus3StokesEigenvalue
  exact mul_nonneg (sq_nonneg (2 * Real.pi)) (torus3ModeSq_nonneg k)

noncomputable def torus3FourierEnergy
    (u : Torus3VectorL2) (c : Fin 3) (k : (Fin 3) → ℤ) : ℝ :=
  ‖mFourierCoeff (u c) k‖ ^ 2

theorem torus3FourierEnergy_nonneg
    (u : Torus3VectorL2) (c : Fin 3) (k : (Fin 3) → ℤ) :
    0 ≤ torus3FourierEnergy u c k := by
  unfold torus3FourierEnergy
  exact sq_nonneg _

noncomputable def torus3L2SpectralSq
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ)) : ℝ :=
  Finset.sum Finset.univ (fun c : Fin 3 =>
    Finset.sum s (fun k => torus3FourierEnergy u c k))

noncomputable def torus3A14SpectralSq
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ)) : ℝ :=
  Finset.sum Finset.univ (fun c : Fin 3 =>
    Finset.sum s (fun k =>
      Real.sqrt (torus3StokesEigenvalue k) *
        torus3FourierEnergy u c k))

noncomputable def torus3PhysicalL2Sq (u : Torus3VectorL2) : ℝ :=
  Finset.sum Finset.univ (fun c : Fin 3 => ∫ t, ‖u c t‖ ^ 2)

noncomputable def torus3CriticalSpectralSq
    (h : ℝ)
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ)) : ℝ :=
  torus3L2SpectralSq u s +
    Real.sqrt h * torus3A14SpectralSq u s

noncomputable def criticalWeight (x : ℝ) : ℝ :=
  1 + Real.sqrt x

theorem finite_stokes_criticalWeight_identity
    {ι : Type*}
    (s : Finset ι)
    (h : ℝ)
    (lambda energy : ι → ℝ)
    (hh : 0 ≤ h)
    (hlambda : ∀ i, 0 ≤ lambda i) :
    Finset.sum s (fun i => criticalWeight (h * lambda i) * energy i)
      =
    Finset.sum s energy
      + Real.sqrt h *
        Finset.sum s (fun i => Real.sqrt (lambda i) * energy i) := by
  calc
    Finset.sum s (fun i => criticalWeight (h * lambda i) * energy i)
        =
      Finset.sum s (fun i =>
        (1 + Real.sqrt h * Real.sqrt (lambda i)) * energy i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [criticalWeight, Real.sqrt_mul hh]
    _ =
      Finset.sum s (fun i =>
        energy i + Real.sqrt h * (Real.sqrt (lambda i) * energy i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ =
      Finset.sum s energy
        + Finset.sum s (fun i =>
            Real.sqrt h * (Real.sqrt (lambda i) * energy i)) := by
          rw [Finset.sum_add_distrib]
    _ =
      Finset.sum s energy
        + Real.sqrt h *
          Finset.sum s (fun i => Real.sqrt (lambda i) * energy i) := by
          rw [Finset.mul_sum]

theorem torus3_criticalWeight_spectral_identity
    (h : ℝ)
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ))
    (hh : 0 ≤ h) :
    Finset.sum Finset.univ (fun c : Fin 3 =>
      Finset.sum s (fun k =>
        criticalWeight (h * torus3StokesEigenvalue k) *
          torus3FourierEnergy u c k))
      =
    torus3CriticalSpectralSq h u s := by
  unfold torus3CriticalSpectralSq torus3L2SpectralSq torus3A14SpectralSq
  have hcomp :
      ∀ c : Fin 3,
        Finset.sum s (fun k =>
          criticalWeight (h * torus3StokesEigenvalue k) *
            torus3FourierEnergy u c k)
        =
        Finset.sum s (fun k => torus3FourierEnergy u c k)
          +
        Real.sqrt h *
          Finset.sum s (fun k =>
            Real.sqrt (torus3StokesEigenvalue k) *
              torus3FourierEnergy u c k) := by
    intro c
    exact finite_stokes_criticalWeight_identity
      s h torus3StokesEigenvalue
      (fun k => torus3FourierEnergy u c k)
      hh torus3StokesEigenvalue_nonneg
  calc
    Finset.sum Finset.univ (fun c : Fin 3 =>
      Finset.sum s (fun k =>
        criticalWeight (h * torus3StokesEigenvalue k) *
          torus3FourierEnergy u c k))
        =
      Finset.sum Finset.univ (fun c : Fin 3 =>
        (Finset.sum s (fun k => torus3FourierEnergy u c k))
          +
        Real.sqrt h *
          Finset.sum s (fun k =>
            Real.sqrt (torus3StokesEigenvalue k) *
              torus3FourierEnergy u c k)) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hcomp c
    _ =
      Finset.sum Finset.univ (fun c : Fin 3 =>
        Finset.sum s (fun k => torus3FourierEnergy u c k))
      +
      Finset.sum Finset.univ (fun c : Fin 3 =>
        Real.sqrt h *
          Finset.sum s (fun k =>
            Real.sqrt (torus3StokesEigenvalue k) *
              torus3FourierEnergy u c k)) := by
          rw [Finset.sum_add_distrib]
    _ =
      Finset.sum Finset.univ (fun c : Fin 3 =>
        Finset.sum s (fun k => torus3FourierEnergy u c k))
      +
      Real.sqrt h *
        Finset.sum Finset.univ (fun c : Fin 3 =>
          Finset.sum s (fun k =>
            Real.sqrt (torus3StokesEigenvalue k) *
              torus3FourierEnergy u c k)) := by
          congr 1
          rw [Finset.mul_sum]

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

theorem torus3_l2_spectral_eq_physical
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ))
    (hzero :
      ∀ c : Fin 3, ∀ k, k ∉ s → mFourierCoeff (u c) k = 0) :
    torus3L2SpectralSq u s = torus3PhysicalL2Sq u := by
  unfold torus3L2SpectralSq torus3PhysicalL2Sq torus3FourierEnergy
  apply Finset.sum_congr rfl
  intro c hc
  exact torus_scalar_finite_parseval (u c) s (hzero c)

theorem torus3_stokes_quarter_dictionary
    (h : ℝ)
    (u : Torus3VectorL2)
    (s : Finset ((Fin 3) → ℤ))
    (hh : 0 ≤ h)
    (hzero :
      ∀ c : Fin 3, ∀ k, k ∉ s → mFourierCoeff (u c) k = 0) :
    Finset.sum Finset.univ (fun c : Fin 3 =>
      Finset.sum s (fun k =>
        criticalWeight (h * torus3StokesEigenvalue k) *
          torus3FourierEnergy u c k))
      =
    torus3PhysicalL2Sq u +
      Real.sqrt h * torus3A14SpectralSq u s := by
  rw [torus3_criticalWeight_spectral_identity h u s hh]
  unfold torus3CriticalSpectralSq
  rw [torus3_l2_spectral_eq_physical u s hzero]

#print axioms CEATheta.torus3ModeSq_nonneg
#print axioms CEATheta.torus3StokesEigenvalue_nonneg
#print axioms CEATheta.finite_stokes_criticalWeight_identity
#print axioms CEATheta.torus3_criticalWeight_spectral_identity
#print axioms CEATheta.torus3_l2_spectral_eq_physical
#print axioms CEATheta.torus3_stokes_quarter_dictionary

end CEATheta
