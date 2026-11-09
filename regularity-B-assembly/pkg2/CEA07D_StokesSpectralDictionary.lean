import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace CEATheta

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
      + Real.sqrt h * Finset.sum s (fun i => Real.sqrt (lambda i) * energy i) := by
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

structure FiniteStokesDictionary (ι : Type*) where
  modes : Finset ι
  h : ℝ
  lambda : ι → ℝ
  energy : ι → ℝ
  l2sq : ℝ
  a14sq : ℝ
  hh : 0 ≤ h
  hlambda : ∀ i, 0 ≤ lambda i
  l2_parseval :
    l2sq = Finset.sum modes energy
  a14_parseval :
    a14sq =
      Finset.sum modes (fun i => Real.sqrt (lambda i) * energy i)

theorem finite_stokes_dictionary_identity
    {ι : Type*}
    (d : FiniteStokesDictionary ι) :
    Finset.sum d.modes
        (fun i => criticalWeight (d.h * d.lambda i) * d.energy i)
      =
    d.l2sq + Real.sqrt d.h * d.a14sq := by
  rw [finite_stokes_criticalWeight_identity
      d.modes d.h d.lambda d.energy d.hh d.hlambda]
  rw [← d.l2_parseval, ← d.a14_parseval]

theorem finite_bkqr_to_stokes_critical
    {ι : Type*}
    (d : FiniteStokesDictionary ι)
    (a M : ℝ)
    (hlower :
      Finset.sum d.modes
          (fun i => criticalWeight (d.h * d.lambda i) * d.energy i)
        ≤ 2 * M)
    (hupper :
      M ≤ a * Finset.sum d.modes
          (fun i => criticalWeight (d.h * d.lambda i) * d.energy i)) :
    (d.l2sq + Real.sqrt d.h * d.a14sq ≤ 2 * M)
      ∧
    (M ≤ a * (d.l2sq + Real.sqrt d.h * d.a14sq)) := by
  constructor
  · rw [← finite_stokes_dictionary_identity d]
    exact hlower
  · rw [← finite_stokes_dictionary_identity d]
    exact hupper

#print axioms CEATheta.finite_stokes_criticalWeight_identity
#print axioms CEATheta.finite_stokes_dictionary_identity
#print axioms CEATheta.finite_bkqr_to_stokes_critical

end CEATheta
