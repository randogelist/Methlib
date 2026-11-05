import WJIDifferentialDomain

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal WJISmooth
open scoped ContDiff
noncomputable section

private theorem smooth_second_partial {q : RSpace → ℝ} (hq : ContDiff ℝ ∞ q)
    (i j : Fin 3) (x : RSpace) :
    spatialDerivative i (spatialDerivative j q) x =
      (fderiv ℝ (fderiv ℝ q) x) (basisDirection i) (basisDirection j) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ q) := (contDiff_infty_iff_fderiv.mp hq).2
  unfold spatialDerivative
  rw [fderiv_clm_apply (c := fderiv ℝ q) (u := fun _ : RSpace => basisDirection j)
    ((contDiff_infty_iff_fderiv.mp hdf).1 x) (by fun_prop)]
  simp

/-- Coordinate partial derivatives commute on indefinitely differentiable real fields. -/
theorem wji_smooth_partial_comm {q : RSpace → ℝ} (hq : ContDiff ℝ ∞ q)
    (i j : Fin 3) :
    spatialDerivative i (spatialDerivative j q) = spatialDerivative j (spatialDerivative i q) := by
  funext x
  rw [smooth_second_partial hq i j x, smooth_second_partial hq j i x]
  have horder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  exact (hq.contDiffAt (x := x)).isSymmSndFDerivAt horder (basisDirection i) (basisDirection j)

private def smoothLap : scalarSpace →ₗ[ℝ] scalarSpace :=
  (partialMap 0).comp (partialMap 0) + (partialMap 1).comp (partialMap 1) +
    (partialMap 2).comp (partialMap 2)

private theorem bundled_partial_comm (f : scalarSpace) (i j : Fin 3) :
    partialMap i (partialMap j f) = partialMap j (partialMap i f) := by
  apply Subtype.ext
  exact wji_smooth_partial_comm f.property i j

theorem wji_lap_partial_comm {q : RSpace → ℝ} (hq : ContDiff ℝ ∞ q) (i : Fin 3) :
    laplacian realAnalysis (spatialDerivative i q) = spatialDerivative i (laplacian realAnalysis q) := by
  let f : scalarSpace := ⟨q, hq⟩
  have move (j : Fin 3) :
      partialMap j (partialMap j (partialMap i f)) = partialMap i (partialMap j (partialMap j f)) :=
    (congrArg (fun g : scalarSpace => partialMap j g) (bundled_partial_comm f j i)).trans
      (bundled_partial_comm (partialMap j f) j i)
  have he : smoothLap (partialMap i f) = partialMap i (smoothLap f) := by
    change partialMap 0 (partialMap 0 (partialMap i f)) +
        partialMap 1 (partialMap 1 (partialMap i f)) + partialMap 2 (partialMap 2 (partialMap i f)) =
      partialMap i (partialMap 0 (partialMap 0 f) + partialMap 1 (partialMap 1 f) +
        partialMap 2 (partialMap 2 f))
    rw [map_add, map_add, move 0, move 1, move 2]
  exact congrArg (fun g : scalarSpace => g.val) he

theorem wji_lap_sub {p q : RSpace → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    laplacian realAnalysis (p - q) = laplacian realAnalysis p - laplacian realAnalysis q :=
  congrArg (fun g : scalarSpace => g.val) (smoothLap.map_sub ⟨p, hp⟩ ⟨q, hq⟩)

end
end CondFeffA
