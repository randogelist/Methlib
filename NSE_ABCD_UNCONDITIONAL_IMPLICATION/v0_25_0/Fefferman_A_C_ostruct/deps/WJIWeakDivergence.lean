import CondRecurrence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory
open scoped BigOperators
noncomputable section

theorem wji_schwartz_partial_memLp (φ : SchwartzMap RSpace ℝ) (i : Fin 3) :
    MemLp (spatialDerivative i (φ : RSpace → ℝ)) 2 volume := by
  let ψ := SchwartzMap.evalCLM ℝ RSpace ℝ (basisDirection i)
    (SchwartzMap.fderivCLM ℝ RSpace ℝ φ)
  exact ψ.memLp 2 volume

/-- The integration-by-parts identity holds for a scalar test with first
derivative in L², including a normalized pressure whenever it has these bounds. -/
theorem wji_coordinate_integration_by_parts_l2 (f φ : RSpace → ℝ) (i : Fin 3)
    (hs : Differentiable ℝ f) (hp : Differentiable ℝ φ)
    (h2 : MemLp f 2 volume) (hp2 : MemLp φ 2 volume)
    (hd : MemLp (spatialDerivative i f) 2 volume)
    (hpd : MemLp (spatialDerivative i φ) 2 volume) :
    (∫ x, f x * spatialDerivative i φ x) = -(∫ x, spatialDerivative i f x * φ x) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := φ) (v := basisDirection i) (μ := volume)
    (hd.integrable_mul hp2) (h2.integrable_mul hpd) (h2.integrable_mul hp2)
    (fun x _ => hs x) (fun x _ => hp x)

theorem wji_coordinate_integration_by_parts (f : RSpace → ℝ) (i : Fin 3)
    (hs : Differentiable ℝ f) (h2 : MemLp f 2 volume)
    (hd : MemLp (spatialDerivative i f) 2 volume) (φ : SchwartzMap RSpace ℝ) :
    (∫ x, f x * spatialDerivative i (φ : RSpace → ℝ) x) =
      -(∫ x, spatialDerivative i f x * φ x) :=
  wji_coordinate_integration_by_parts_l2 f φ i hs (fun _ => φ.differentiableAt)
    h2 (φ.memLp 2 volume) hd (wji_schwartz_partial_memLp φ i)

/-- Classical divergence zero annihilates gradients of differentiable scalar
tests having square-integrable values and coordinate derivatives. -/
theorem wji_divergence_pairing_zero_of_memLp (v : RInitial)
    (hs : ∀ i : Fin 3, Differentiable ℝ (fun x => v x i))
    (h2 : ∀ i : Fin 3, MemLp (fun x => v x i) 2 volume)
    (hd : ∀ i : Fin 3, MemLp (spatialDerivative i (fun x => v x i)) 2 volume)
    (hdiv : fieldDiv v = 0) (φ : RSpace → ℝ) (hp : Differentiable ℝ φ)
    (hp2 : MemLp φ 2 volume) (hpd : ∀ i : Fin 3, MemLp (spatialDerivative i φ) 2 volume) :
    (∑ i : Fin 3, ∫ x, v x i * spatialDerivative i φ x) = 0 := by
  let g (i : Fin 3) (x : RSpace) := spatialDerivative i (fun y => v y i) x * φ x
  have hint (i : Fin 3) : Integrable (g i) := (hd i).integrable_mul hp2
  have hz (x : RSpace) : (∑ i : Fin 3, g i x) = 0 := by
    dsimp only [g]
    rw [← Finset.sum_mul, Fin.sum_univ_three]
    have he := congrFun hdiv x
    change spatialDerivative 0 (fun y => v y 0) x + spatialDerivative 1 (fun y => v y 1) x +
      spatialDerivative 2 (fun y => v y 2) x = 0 at he
    rw [he, zero_mul]
  calc
    _ = ∑ i : Fin 3, -(∫ x, g i x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact wji_coordinate_integration_by_parts_l2 (fun x => v x i) φ i (hs i) hp
        (h2 i) hp2 (hd i) (hpd i)
    _ = -(∑ i : Fin 3, ∫ x, g i x) := by rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : Fin 3, g i x) := by
      rw [integral_finsetSum Finset.univ (f := g) (fun i _ => hint i)]
    _ = 0 := by simp only [hz, integral_zero, neg_zero]

theorem wji_divergence_pairing_zero (v : RInitial)
    (hs : ∀ i : Fin 3, Differentiable ℝ (fun x => v x i))
    (h2 : ∀ i : Fin 3, MemLp (fun x => v x i) 2 volume)
    (hd : ∀ i : Fin 3, MemLp (spatialDerivative i (fun x => v x i)) 2 volume)
    (hdiv : fieldDiv v = 0) (φ : SchwartzMap RSpace ℝ) :
    (∑ i : Fin 3, ∫ x, v x i * spatialDerivative i (φ : RSpace → ℝ) x) = 0 :=
  wji_divergence_pairing_zero_of_memLp v hs h2 hd hdiv φ (fun _ => φ.differentiableAt)
    (φ.memLp 2 volume) (wji_schwartz_partial_memLp φ)

theorem wji_divergence_integral_zero (v : RInitial)
    (hs : ∀ i : Fin 3, Differentiable ℝ (fun x => v x i))
    (h2 : ∀ i : Fin 3, MemLp (fun x => v x i) 2 volume)
    (hd : ∀ i : Fin 3, MemLp (spatialDerivative i (fun x => v x i)) 2 volume)
    (hdiv : fieldDiv v = 0) (φ : SchwartzMap RSpace ℝ) :
    (∫ x, ∑ i : Fin 3, v x i * spatialDerivative i (φ : RSpace → ℝ) x) = 0 := by
  rw [integral_finsetSum Finset.univ (f := fun i x => v x i * spatialDerivative i (φ : RSpace → ℝ) x)
    (fun i _ => (h2 i).integrable_mul (wji_schwartz_partial_memLp φ i))]
  exact wji_divergence_pairing_zero v hs h2 hd hdiv φ

end
end CondFeffA
