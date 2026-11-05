import WJINewtonPoisson
import WJISmoothCommutation
import WJIWeakDivergence

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

private lemma wji_coordinate_decomposition (v : RSpace) :
    (∑ j : Fin 3, v j • basisDirection j) = v := by
  funext i
  simp [basisDirection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]

private lemma wji_volume_univ : volume (Set.univ : Set RSpace) = ⊤ := by
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) Set.univ = ⊤
  rw [Measure.pi_univ]
  simp [Real.volume_univ, Fin.prod_univ_three]

/-- An entire harmonic scalar in the concrete all-order L² space vanishes.
Integration by parts controls each coordinate derivative. -/
theorem wji_harmonic_scalar_zero (f : RSpace → ℝ) (hf : f ∈ WJISobolev.scalar)
    (hlap : laplacian realAnalysis f = 0) : f = 0 := by
  let d (j : Fin 3) := spatialDerivative j f
  have hdm (j : Fin 3) : d j ∈ WJISobolev.scalar := WJISobolev.scalar_partial hf j
  have hd2 (j : Fin 3) := (WJISobolev.scalar_memLp (hdm j)).1
  have hdd (j : Fin 3) := (WJISobolev.scalar_memLp (WJISobolev.scalar_partial (hdm j) j)).1
  have hf2 := (WJISobolev.scalar_memLp hf).1
  have hdiff := (WJISobolev.scalar_smooth hf).differentiable (by simp)
  let b (j : Fin 3) := ∫ x, d j x * d j x
  let g (j : Fin 3) (x : RSpace) := spatialDerivative j (d j) x * f x
  have bg (j : Fin 3) : b j = -(∫ x, g j x) :=
    wji_coordinate_integration_by_parts_l2 (d j) f j
      ((WJISobolev.scalar_smooth (hdm j)).differentiable (by simp)) hdiff
      (hd2 j) hf2 (hdd j) (hd2 j)
  have gi (j : Fin 3) : Integrable (g j) := (hdd j).integrable_mul hf2
  have gz (x : RSpace) : (∑ j : Fin 3, g j x) = 0 := by
    dsimp only [g]
    rw [← Finset.sum_mul, Fin.sum_univ_three]
    have hx := congrFun hlap x
    change spatialDerivative 0 (d 0) x + spatialDerivative 1 (d 1) x +
      spatialDerivative 2 (d 2) x = 0 at hx
    rw [hx, zero_mul]
  have bz : (∑ j : Fin 3, b j) = 0 := by
    calc
      _ = ∑ j : Fin 3, -(∫ x, g j x) := Finset.sum_congr rfl (fun j _ => bg j)
      _ = -(∫ x, ∑ j : Fin 3, g j x) := by
        rw [Finset.sum_neg_distrib, integral_finsetSum Finset.univ (f := g) (fun j _ => gi j)]
      _ = 0 := by simp only [gz, integral_zero, neg_zero]
  have bn (j : Fin 3) : 0 ≤ b j := integral_nonneg (fun x => mul_self_nonneg (d j x))
  have djzero (j : Fin 3) (x : RSpace) : d j x = 0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => bn j)).mp bz j (Finset.mem_univ j)
    have ae := (integral_eq_zero_iff_of_nonneg (f := fun y => d j y * d j y)
      (fun y => mul_self_nonneg _) ((hd2 j).integrable_mul (hd2 j))).mp he
    have hc := (WJISobolev.scalar_smooth (hdm j)).continuous
    have hz := MeasureTheory.Measure.eq_of_ae_eq ae (hc.mul hc)
      (continuous_const : Continuous (0 : RSpace → ℝ))
    exact mul_self_eq_zero.mp (congrFun hz x)
  have fd (x : RSpace) : fderiv ℝ f x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change (fderiv ℝ f x) v = 0
    calc
      _ = (fderiv ℝ f x) (∑ j : Fin 3, v j • basisDirection j) :=
        congrArg (fun t => (fderiv ℝ f x) t) (wji_coordinate_decomposition v).symm
      _ = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j _
        rw [map_smul]
        change v j • d j x = 0
        rw [djzero, smul_zero]
  have he : f = fun _ : RSpace => f 0 :=
    funext fun x => is_const_of_fderiv_eq_zero hdiff fd x (0 : RSpace)
  have hconst : MemLp (fun _ : RSpace => f 0) 2 volume := he ▸ hf2
  have h0 : f 0 = 0 := by
    rcases (memLp_const_iff (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp hconst with hz | hfin
    · exact hz
    · rw [wji_volume_univ] at hfin
      exact (lt_irrefl _ hfin).elim
  exact he.trans (funext fun _ => h0)

/-- Equal Laplacians of two smooth potentials determine the same gradient
when their gradient difference belongs to the concrete Sobolev field space. -/
theorem wji_equal_gradients_of_laplacian (p q : RSpace → ℝ)
    (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hgrad : wjiScalarGradient p - wjiScalarGradient q ∈ WJISobolev.space)
    (he : laplacian realAnalysis p = laplacian realAnalysis q) :
    wjiScalarGradient p = wjiScalarGradient q := by
  funext x i
  let f := spatialDerivative i p - spatialDerivative i q
  have hf : f ∈ WJISobolev.scalar := hgrad i
  have hdp : ContDiff ℝ ∞ (spatialDerivative i p) :=
    (WJISmooth.partialMap i (⟨p, hp⟩ : WJISmooth.scalarSpace)).property
  have hdq : ContDiff ℝ ∞ (spatialDerivative i q) :=
    (WJISmooth.partialMap i (⟨q, hq⟩ : WJISmooth.scalarSpace)).property
  have hzero : laplacian realAnalysis f = 0 := by
    change laplacian realAnalysis (spatialDerivative i p - spatialDerivative i q) = 0
    rw [wji_lap_sub hdp hdq, wji_lap_partial_comm hp i, wji_lap_partial_comm hq i, he, sub_self]
  exact sub_eq_zero.mp (congrFun (wji_harmonic_scalar_zero f hf hzero) x)

end
end CondFeffA
