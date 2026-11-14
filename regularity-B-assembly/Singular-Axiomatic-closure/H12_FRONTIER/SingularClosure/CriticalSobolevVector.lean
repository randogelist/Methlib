import SingularClosure.CriticalComplexSobolev
import SingularClosure.CriticalFourierInterpolation

/-! Finite-dimensional passage from complex scalar interpolation to velocity. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SingularClosure
noncomputable section

theorem critical_finiteSynthesis_norm_le_components
    (N : ℕ) (c : FourierCoeff) (x : Vec) :
    ‖finiteSynthesis N c x‖ ≤ ∑ j : Fin 3, ‖complexFiniteSynthesis N c j x‖ := by
  have hsq (j : Fin 3) : (finiteSynthesis N c x j) ^ 2 ≤
      ‖complexFiniteSynthesis N c j x‖ ^ 2 := by
    change (complexFiniteSynthesis N c j x).re ^ 2 ≤ _
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (complexFiniteSynthesis N c j x).im]
  have hv := EuclideanSpace.real_norm_sq_eq (finiteSynthesis N c x)
  simp [Fin.sum_univ_succ] at hv ⊢
  have h0 := norm_nonneg (complexFiniteSynthesis N c 0 x)
  have h1 := norm_nonneg (complexFiniteSynthesis N c 1 x)
  have h2 := norm_nonneg (complexFiniteSynthesis N c 2 x)
  have hv0 := norm_nonneg (finiteSynthesis N c x)
  have hc0 := hsq 0
  have hc1 := hsq 1
  have hc2 := hsq 2
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

theorem critical_vector_L3_of_scalar
    {C : ℝ≥0∞}
    (hscalar : ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 3 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ))
    (N : ℕ) (c : FourierCoeff) :
    eLpNorm (finiteSynthesis N c) 3 (volume.restrict unitCube) ≤
      (3 * C) * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) := by
  have hmeas (j : Fin 3) : AEStronglyMeasurable
      (fun x => ‖complexFiniteSynthesis N c j x‖) (volume.restrict unitCube) :=
    (complexFiniteSynthesis_continuous N c j).norm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => ∑ j : Fin 3, ‖complexFiniteSynthesis N c j x‖)
        3 (volume.restrict unitCube) :=
      eLpNorm_mono_real (critical_finiteSynthesis_norm_le_components N c)
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => ‖complexFiniteSynthesis N c j x‖)
        3 (volume.restrict unitCube) := by
      have hsum : (fun x => ∑ j : Fin 3, ‖complexFiniteSynthesis N c j x‖) =
          ∑ j : Fin 3, (fun x => ‖complexFiniteSynthesis N c j x‖) := by
        funext x
        simp only [Finset.sum_apply]
      rw [hsum]
      exact eLpNorm_sum_le (s := Finset.univ) (fun j _ => hmeas j) (by norm_num)
    _ = ∑ j : Fin 3, eLpNorm (complexFiniteSynthesis N c j)
        3 (volume.restrict unitCube) := by simp only [eLpNorm_norm]
    _ ≤ ∑ _j : Fin 3,
        C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun j _ => hscalar N c j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      <;> ring

end
end SingularClosure
