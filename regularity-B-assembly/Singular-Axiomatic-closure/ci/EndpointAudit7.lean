import SingularClosure.StrongSobolevRealization
open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff Interval ENNReal
noncomputable section
example : ∀ (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T),
∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ContinuousOn (g.sobolevState 1) (Ici 0) ∧
      MemLp (g.sobolevState 1) ⊤ (volume.restrict (Icc (0 : ℝ) T)) ∧
      MemLp (g.sobolevState 2) 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      MemLp (g.rhsSobolev 0) 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (g.sobolevState 0)
        (g.rhsSobolev 0 t) (Ici 0) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState 1 t‖ ^ 2 ≤ B) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ B ∧
      IntervalIntegrable (fun t => ‖g.rhsSobolev 0 t‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ‖g.rhsSobolev 0 t‖ ^ 2) ≤ B ∧
      IntervalIntegrable (fun t => ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, ∫ x in unitCube,
        ‖timeDerivative g.velocity t x‖ ^ 2) ≤ B := @SingularClosure.AX6_UNIFORM_STRONG_BOUNDS
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.AX6_UNIFORM_STRONG_BOUNDS"
#check @SingularClosure.AX6_UNIFORM_STRONG_BOUNDS
#print axioms SingularClosure.AX6_UNIFORM_STRONG_BOUNDS
end
