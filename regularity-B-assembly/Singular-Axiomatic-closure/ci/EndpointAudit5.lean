import SingularClosure.EnstrophyAbsorption
open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff
noncomputable section
example : ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t → ∃ d : ℝ,
        HasDerivWithinAt
          (fun r => ∫ x in unitCube, gradientSquareDensity (g.velocity r) x)
          d (Ici 0) t ∧
        d + ν * (∫ x in unitCube, ‖laplacian (g.velocity t) x‖ ^ 2) ≤
          C / ν ^ 3 * (∫ x in unitCube, gradientSquareDensity (g.velocity t) x) ^ 3 := @SingularClosure.GALERKIN_ENSTROPHY_INEQUALITY
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GALERKIN_ENSTROPHY_INEQUALITY"
#check @SingularClosure.GALERKIN_ENSTROPHY_INEQUALITY
#print axioms SingularClosure.GALERKIN_ENSTROPHY_INEQUALITY
end
