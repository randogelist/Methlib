import CondJets
import Mathlib

namespace CondFeffA

open MeasureTheory
open scoped BigOperators Polynomial

/-- Amplitudes on the small interval satisfying the jet bound with one fixed constant. -/
def jetLevel (P : ℕ → ℝ[X]) (δ : ℝ) (m : ℕ) : Set ℝ :=
  {c | c ∈ Set.Ioo 0 δ ∧
    ∀ n, |(P n).eval c| ≤ (n.factorial : ℝ) * (m : ℝ) ^ (n + 1)}

/-- A positive-measure jet level would give one factorial-exponential bound
on the linear coefficients for the entire sequence of amplitude polynomials. -/
def PositiveMeasureInterpolation (P : ℕ → ℝ[X]) (δ : ℝ) : Prop :=
  ∀ m : ℕ, volume (jetLevel P δ m) ≠ 0 →
    FactorialJetBound (fun n => (P n).coeff 1)

/-- A finite-node sufficient condition for positive-measure interpolation.
The remaining estimate concerns only Lagrange basis polynomials and the
geometry of their nodes, not the solution of the PDE. -/
def InterpolationNodeBound (P : ℕ → ℝ[X]) (δ : ℝ) : Prop :=
  ∀ m : ℕ, volume (jetLevel P δ m) ≠ 0 →
    ∃ B : ℕ, ∀ n : ℕ, ∃ s : Finset ℝ,
      (∀ x ∈ s, x ∈ jetLevel P δ m) ∧
      (P n).degree < (s.card : WithBot ℕ) ∧
      ∑ x ∈ s, |(Lagrange.basis s id x).coeff 1| ≤ (B : ℝ) ^ (n + 1)

/-- The linear coefficient is recovered by ordinary finite Lagrange interpolation. -/
theorem linear_coeff_eq_lagrange_sum (p : ℝ[X]) (s : Finset ℝ)
    (hd : p.degree < (s.card : WithBot ℕ)) :
    p.coeff 1 = ∑ x ∈ s, p.eval x * (Lagrange.basis s id x).coeff 1 := by
  have hi : Set.InjOn (id : ℝ → ℝ) (↑s : Set ℝ) := fun _ _ _ _ h => h
  have he := congrArg (fun q : ℝ[X] => q.coeff 1) (Lagrange.eq_interpolate hi hd)
  first
  | simpa only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, id_eq] using he
  | simpa only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul, id_eq] using he

theorem positiveMeasureInterpolation_of_nodes {P : ℕ → ℝ[X]} {δ : ℝ}
    (h : InterpolationNodeBound P δ) : PositiveMeasureInterpolation P δ := by
  intro m hm
  obtain ⟨B, hB⟩ := h m hm
  refine ⟨m * B, ?_⟩
  intro n
  obtain ⟨s, hs, hd, hweight⟩ := hB n
  let A : ℝ := (n.factorial : ℝ) * (m : ℝ) ^ (n + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hvalue (x : ℝ) (hx : x ∈ s) : |(P n).eval x| ≤ A := (hs x hx).2 n
  let w := fun x : ℝ => (Lagrange.basis s id x).coeff 1
  calc
    |(P n).coeff 1| = |∑ x ∈ s, (P n).eval x * w x| :=
      congrArg abs (linear_coeff_eq_lagrange_sum (P n) s hd)
    _ ≤ ∑ x ∈ s, |(P n).eval x * w x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, A * |w x| := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hvalue x hx) (abs_nonneg _)
    _ = A * ∑ x ∈ s, |w x| := by rw [Finset.mul_sum]
    _ ≤ A * (B : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left hweight hA
    _ = (n.factorial : ℝ) * ((m * B : ℕ) : ℝ) ^ (n + 1) := by
      simp only [A, Nat.cast_mul, mul_pow, mul_assoc]

theorem ae_jet_obstruction {P : ℕ → ℝ[X]} {δ : ℝ}
    (hinter : PositiveMeasureInterpolation P δ)
    (hgrowth : ∀ n : ℕ, (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) ≤ |(P n).coeff 1|) :
    ∀ᵐ c : ℝ, c ∈ Set.Ioo 0 δ →
      ¬ FactorialJetBound (fun n => (P n).eval c) := by
  have hbad := linear_jet_growth_excludes_factorial_bound hgrowth
  have hnull (m : ℕ) : volume (jetLevel P δ m) = 0 := by
    by_contra h
    exact hbad (hinter m h)
  have hlevels : ∀ᵐ c : ℝ, ∀ m : ℕ, c ∉ jetLevel P δ m := by
    apply ae_all_iff.mpr
    intro m
    exact measure_eq_zero_iff_ae_notMem.mp (hnull m)
  filter_upwards [hlevels] with c hc
  intro hI hb
  obtain ⟨m, hm⟩ := hb
  exact hc m ⟨hI, hm⟩

theorem exists_small_obstructing_amplitude {P : ℕ → ℝ[X]} {δ : ℝ}
    (hδ : 0 < δ) (hinter : PositiveMeasureInterpolation P δ)
    (hgrowth : ∀ n : ℕ, (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) ≤ |(P n).coeff 1|) :
    ∃ c ∈ Set.Ioo 0 δ, ¬ FactorialJetBound (fun n => (P n).eval c) := by
  have hvol : volume (Set.Ioo 0 δ) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hδ).ne'
  have hfreq : ∃ᵐ c : ℝ, c ∈ Set.Ioo 0 δ := frequently_ae_mem_iff.mpr hvol
  obtain ⟨c, hc, hj⟩ :=
    (hfreq.and_eventually (ae_jet_obstruction hinter hgrowth)).exists
  exact ⟨c, hc, hj hc⟩

/-- Greedy selection in a set of positive outer measure. The complement of the
previous balls supplies a new node; no measurability assumption on E is used. -/
theorem exists_separated_nodes (E : Set ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r)
    (hbudget : ∀ s : Finset ℝ, s.card < N →
      (∑ x ∈ s, volume (Metric.ball x r)) < volume E) :
    ∃ s : Finset ℝ, s.card = N ∧ (∀ x ∈ s, x ∈ E) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y := by
  classical
  have build (k : ℕ) : k ≤ N →
      ∃ s : Finset ℝ, s.card = k ∧ (∀ x ∈ s, x ∈ E) ∧
        ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y := by
    induction k with
    | zero =>
      intro _
      exact ⟨∅, by simp, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hcard, hs, hsep⟩ := ih (by omega)
      have hn : ∃ x ∈ E, ∀ y ∈ s, r ≤ dist x y := by
        by_contra! h
        have hsub : E ⊆ ⋃ y ∈ s, Metric.ball y r := by
          intro x hx
          obtain ⟨y, hy, hdist⟩ := h x hx
          exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hdist⟩⟩
        have hle := (measure_mono (μ := volume) hsub).trans
          (measure_biUnion_finset_le s (fun y => Metric.ball y r))
        exact (not_lt_of_ge hle) (hbudget s (by omega))
      obtain ⟨x, hx, hfar⟩ := hn
      have hnew : x ∉ s := by
        intro hxs
        have ht := hfar x hxs
        rw [dist_self] at ht
        linarith
      refine ⟨insert x s, by simp [hnew, hcard], ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with hyx | hys
        · simpa only [hyx] using hx
        · exact hs y hys
      · intro y hy z hz hyz
        rcases Finset.mem_insert.mp hy with hyx | hys
        · rcases Finset.mem_insert.mp hz with hzx | hzs
          · exact (hyz (hyx.trans hzx.symm)).elim
          · simpa only [hyx] using hfar z hzs
        · rcases Finset.mem_insert.mp hz with hzx | hzs
          · rw [hzx, dist_comm y x]
            exact hfar y hys
          · exact hsep y hys z hzs hyz
  exact build N (le_refl _)

end CondFeffA

#print axioms CondFeffA.linear_coeff_eq_lagrange_sum
#print axioms CondFeffA.positiveMeasureInterpolation_of_nodes
#print axioms CondFeffA.ae_jet_obstruction
#print axioms CondFeffA.exists_small_obstructing_amplitude
#print axioms CondFeffA.exists_separated_nodes
