import Mathlib

namespace CondFeffA

/-- The right-hand time jet at the initial time. Values at negative times
do not enter this derivative. -/
noncomputable def rightJet (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  iteratedDerivWithin n f (Set.Ici 0) 0

/-- An analytic spacetime field on the closed half-space restricts to an
analytic scalar germ within the positive time ray at the spatial origin. -/
theorem analyticWithinAt_of_closedHalfSpace
    (F : (Fin 3 → ℝ) → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ => F z.1 z.2)
      {z | 0 ≤ z.2}) :
    AnalyticWithinAt ℝ (F 0) (Set.Ici 0) 0 := by
  have line : ContDiff ℝ ⊤ (fun t : ℝ => ((0 : Fin 3 → ℝ), t)) :=
    contDiff_const.prodMk contDiff_id
  have along : ContDiffOn ℝ ⊤ (F 0) (Set.Ici 0) :=
    hF.comp line.contDiffOn (fun _ ht => ht)
  exact (along 0 (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)).analyticWithinAt

/-- One-sided analyticity forces a single factorial-geometric upper bound
for every right-hand derivative. -/
theorem rightJet_bound_of_analyticWithinAt (f : ℝ → ℝ)
    (hf : AnalyticWithinAt ℝ f (Set.Ici 0) 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      |rightJet f n| ≤ (n.factorial : ℝ) * M ^ (n + 1) := by
  obtain ⟨g, heq, hg⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  have jets (n : ℕ) : rightJet f n = iteratedDeriv n g 0 := by
    unfold rightJet
    calc
      iteratedDerivWithin n f (Set.Ici 0) 0 =
          iteratedDerivWithin n g (Set.Ici 0) 0 :=
        Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert n heq
      _ = iteratedDeriv n g 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hg.contDiffAt (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)
  let p := FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => iteratedDeriv n g 0 / (n.factorial : ℝ))
  have hp : 0 < p.radius := hg.hasFPowerSeriesAt.radius_pos
  obtain ⟨C, r, hC, hr, bound⟩ := p.le_mul_pow_of_radius_pos hp
  refine ⟨max C r, hC.trans_le (le_max_left C r), ?_⟩
  intro n
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have coef : |iteratedDeriv n g 0| / (n.factorial : ℝ) ≤ C * r ^ n := by
    simpa only [p, FormalMultilinearSeries.ofScalars_norm,
      Real.norm_eq_abs, abs_div, abs_of_pos hfac] using bound n
  have increase : C * r ^ n ≤ max C r * (max C r) ^ n :=
    mul_le_mul (le_max_left C r)
      (pow_le_pow_left₀ hr.le (le_max_right C r) n)
      (pow_nonneg hr.le n) (hC.le.trans (le_max_left C r))
  rw [jets n]
  calc
    |iteratedDeriv n g 0| ≤ (C * r ^ n) * (n.factorial : ℝ) :=
      (div_le_iff₀ hfac).mp coef
    _ ≤ (max C r * (max C r) ^ n) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right increase hfac.le
    _ = (n.factorial : ℝ) * (max C r) ^ (n + 1) := by rw [pow_succ]; ring

theorem rightJet_bound_of_closedHalfSpace
    (F : (Fin 3 → ℝ) → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (fun z : (Fin 3 → ℝ) × ℝ => F z.1 z.2)
      {z | 0 ≤ z.2}) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      |rightJet (F 0) n| ≤ (n.factorial : ℝ) * M ^ (n + 1) :=
  rightJet_bound_of_analyticWithinAt _ (analyticWithinAt_of_closedHalfSpace F hF)

end CondFeffA
