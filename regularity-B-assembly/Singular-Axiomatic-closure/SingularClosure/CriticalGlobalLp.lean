import Mathlib

/-!
# Global time integrability from a uniform local square budget

The positive half-line is exhausted by the actual intervals `(0, n + 1]`.
Local strong measurability and the uniform nonnegative integral bound imply
global strong measurability and a finite global square integral.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ENNReal

namespace SingularClosure

noncomputable section

/-- Uniform local L2 membership and one common square budget imply genuine
global L2 membership on positive time, with the same integral bound. -/
theorem critical_global_L2_of_uniform_local
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (B : ℝ) (hB : 0 ≤ B)
    (hlocal : ∀ T : ℝ, 0 < T →
      MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖f t‖ ^ 2) ≤ B) :
    MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) ≤ B := by
  have hlocalIoc (n : ℕ) :
      MemLp f 2 (volume.restrict (Ioc (0 : ℝ) ((n : ℝ) + 1))) ∧
        (∫ t in Ioc (0 : ℝ) ((n : ℝ) + 1), ‖f t‖ ^ 2) ≤ B := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using
      hlocal ((n : ℝ) + 1) (by positivity)
  have hcover : (⋃ n : ℕ, Ioc (0 : ℝ) ((n : ℝ) + 1)) = Ioi (0 : ℝ) := by
    apply iUnion_Ioc_eq_Ioi_self_iff.mpr
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact ⟨n, by linarith⟩
  have hmono : Monotone (fun n : ℕ => Ioc (0 : ℝ) ((n : ℝ) + 1)) := by
    intro m n hmn t ht
    refine ⟨ht.1, ht.2.trans ?_⟩
    exact add_le_add (by exact_mod_cast hmn) (le_refl 1)
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) := by
    rw [← hcover]
    exact AEStronglyMeasurable.iUnion
      (fun n => (hlocalIoc n).1.aestronglyMeasurable)
  have hlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖f t‖ ^ 2)) ≤
      ENNReal.ofReal B := by
    rw [← hcover, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro n
    have hi : Integrable (fun t => ‖f t‖ ^ 2)
        (volume.restrict (Ioc (0 : ℝ) ((n : ℝ) + 1))) :=
      (memLp_two_iff_integrable_sq_norm (hlocalIoc n).1.aestronglyMeasurable).mp
        (hlocalIoc n).1
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖f t‖))]
    exact ENNReal.ofReal_le_ofReal (hlocalIoc n).2
  have hsquare : Integrable (fun t => ‖f t‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine ⟨hmeas.norm.pow 2, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun t => sq_nonneg ‖f t‖))).mpr
        (hlin.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).mpr hsquare, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ofReal_integral_eq_lintegral_ofReal hsquare
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖f t‖))]
  exact hlin

end

end SingularClosure
