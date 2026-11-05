import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

noncomputable section

open Set

namespace CondFeffB

/-- A real analytic right germ bounds its normalized, one-sided Taylor coefficients. -/
theorem analyticRight_normalized_bound {f : ℝ → ℝ}
    (ha : AnalyticWithinAt ℝ f (Ici 0) 0) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧ ∀ n : ℕ,
      |iteratedDerivWithin n f (Ici 0) 0| / (n.factorial : ℝ) ≤ C * M ^ n := by
  obtain ⟨g, _, heq, ha_g⟩ := analyticWithinAt_iff_exists_analyticAt'.mp ha
  have hfg : EqOn f g (Ici 0) := fun t ht => heq (mem_insert_of_mem _ ht)
  obtain ⟨p, r, hseries⟩ := ha_g
  obtain ⟨C, M, hC, hM, hp⟩ := p.le_mul_pow_of_radius_pos hseries.radius_pos
  refine ⟨C, M, hC, hM, ?_⟩
  intro n
  have hjet : iteratedDerivWithin n f (Ici 0) 0 = iteratedDeriv n g 0 := by
    calc
      iteratedDerivWithin n f (Ici 0) 0 = iteratedDerivWithin n g (Ici 0) 0 := by
        unfold iteratedDerivWithin
        rw [iteratedFDerivWithin_congr hfg (self_mem_Ici : (0 : ℝ) ∈ Ici 0) n]
      _ = iteratedDeriv n g 0 := iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ici 0) hseries.analyticAt.contDiffAt self_mem_Ici
  have hfactor : iteratedDeriv n g 0 =
      (n.factorial : ℝ) * p n (fun _ => (1 : ℝ)) := by
    simpa only [iteratedDeriv, nsmul_eq_mul] using (hseries.factorial_smul (1 : ℝ) n).symm
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hnorm : |p n (fun _ => (1 : ℝ))| ≤ ‖p n‖ := by
    simpa [Real.norm_eq_abs] using
      (p n).le_opNorm (fun _ => (1 : ℝ))
  rw [hjet, hfactor, abs_mul, abs_of_pos hn]
  calc
    (n.factorial : ℝ) * |p n (fun _ => (1 : ℝ))| / (n.factorial : ℝ) =
        |p n (fun _ => (1 : ℝ))| := by field_simp [ne_of_gt hn] <;> ring
    _ ≤ ‖p n‖ := hnorm
    _ ≤ C * M ^ n := hp n

/-- Restrict joint closed-half-space analyticity to the time line at a fixed spatial point. -/
theorem analyticTimeTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} (x : E)
    (hF : ContDiffOn ℝ ⊤ F {z : E × ℝ | 0 ≤ z.2}) :
    AnalyticWithinAt ℝ (fun t => F (x,t)) (Ici 0) 0 := by
  have hMap : MapsTo (fun t : ℝ => (x,t)) (Ici 0) {z : E × ℝ | 0 ≤ z.2} :=
    fun _ ht => ht
  have hc : ContDiffOn ℝ ⊤ (fun t => F (x,t)) (Ici 0) :=
    hF.comp (contDiff_prodMk_right x).contDiffOn hMap
  exact hc.analyticOn _ self_mem_Ici

end CondFeffB
