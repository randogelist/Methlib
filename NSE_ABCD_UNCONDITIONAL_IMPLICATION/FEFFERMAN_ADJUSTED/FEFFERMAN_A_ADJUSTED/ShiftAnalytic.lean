import ConcreteABCDUnifiedClosure

set_option autoImplicit false

namespace Fefferman.ConcreteReal.AdjustedA

/-- A positive time shift places the closed half-space inside the open analytic domain. -/
theorem smoothClosedHalfSpaceReal_shift
    (f : RSpace → ℝ → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hf : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => f z.1 z.2)
      {z : RSpace × ℝ | 0 < z.2}) :
    smoothClosedHalfSpaceReal (fun x t => f x (t + τ)) := by
  let shift : RSpace × ℝ → RSpace × ℝ := fun z => (z.1, z.2 + τ)
  have hshift : ContDiff ℝ ⊤ shift :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hmaps : Set.MapsTo shift {z : RSpace × ℝ | 0 ≤ z.2}
      {z : RSpace × ℝ | 0 < z.2} := by
    intro z hz
    change 0 ≤ z.2 at hz
    change 0 < z.2 + τ
    exact add_pos_of_nonneg_of_pos hz hτ
  change ContDiffOn ℝ ⊤ ((fun z : RSpace × ℝ => f z.1 z.2) ∘ shift)
    {z : RSpace × ℝ | 0 ≤ z.2}
  exact hf.comp hshift.contDiffOn hmaps

end Fefferman.ConcreteReal.AdjustedA
