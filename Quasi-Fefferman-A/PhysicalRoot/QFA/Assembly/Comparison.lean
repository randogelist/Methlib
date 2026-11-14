import QFA.Endpoints.Comparison.AdmissibleTimes
import QFA.Endpoints.Comparison.RelativeEnergy

/-!
# QFA comparison assembly

Status: A_TIER_CANDIDATE. Mathlib pin
db584cd6d46c92f209a44c0f1c829460d327499d; external Lean 4.33.0.
No local Lean or Lake execution. External compiler and exact axiom audit
remain pending.

D09.03--D09.04: LE026/EP095 constructs admissible positive times; LE030/EP096
then yields comparison. The user of this assembly supplies neither a sequence
of admissible starts nor a numerical upper bound for the coefficient integral.
The full-measure predicate, common strong right traces, coefficient/product
integrability, and actual relative-energy inequality remain explicit premises.

No weak NSE cross-testing identity, physical Leray--Hopf membership, or PDE
regularity is supplied by these generic normed-space implications. The final
set-theoretic endpoint identifies only restrictions to nonnegative time;
auxiliary negative-time extensions are not identified.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace QFA.Assembly.Comparison

/-- D09.03--D09.04: a.e. valid starts and common right traces supply every
sequence and budget premise of the existing norm-valued comparison theorem.

The upper endpoint `T` is included in the conclusion. The admissible starts
are selected strictly below `T`, matching the supplied `Ioo` start condition.
-/
theorem eq_on_Ioc_of_ae_relative_energy
    {V : Type*} [NormedAddCommGroup V]
    {u v : ℝ → V} {g : ℝ → ℝ} {a₀ : V} {T : ℝ} {Good : ℝ → Prop}
    (hT : 0 < T)
    (hg : ContinuousOn g (Ioc (0 : ℝ) T))
    (hg_nonneg : ∀ t ∈ Ioc (0 : ℝ) T, 0 ≤ g t)
    (hg_integrable : IntervalIntegrable g volume (0 : ℝ) T)
    (hprod : IntervalIntegrable
      (fun r => g r * ‖u r - v r‖ ^ 2) volume (0 : ℝ) T)
    (hgood : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) T), Good s)
    (hu_trace : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hv_trace : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hrelative : ∀ s ∈ Ioo (0 : ℝ) T, Good s →
      ∀ t ∈ Icc s T,
        ‖u t - v t‖ ^ 2 ≤ ‖u s - v s‖ ^ 2 +
          ∫ r in s..t, g r * ‖u r - v r‖ ^ 2) :
    ∀ t ∈ Ioc (0 : ℝ) T, u t = v t := by
  -- EP011: null endpoint conversion retains the strict start bound.
  have hgoodIoc : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T),
      s < T ∧ Good s := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hgood] with s hs hgs
    exact ⟨hs.2, hgs⟩
  -- LE026 / EP095: the sequence is constructed, not assumed by the caller.
  obtain ⟨ε, hε, hε_zero⟩ :=
    QFA.Endpoints.Comparison.CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO
      hT (fun s => s < T ∧ Good s) hgoodIoc
  have hε_right : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hε_zero, Filter.Eventually.of_forall (fun n => (hε n).1.1)⟩
  -- LE030 / EP096: M is the actual finite coefficient integral, so its
  -- budget premise is reflexive. Integrability is retained separately.
  apply QFA.Endpoints.Comparison.CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE
    (u := u) (v := v) (a := g) (a₀ := a₀)
    (M := ∫ r in (0 : ℝ)..T, g r) (ε := ε)
    hT hg hg_nonneg hg_integrable hprod le_rfl
    (fun n => (hε n).1) hε_zero
    (hu_trace.comp hε_right) (hv_trace.comp hε_right)
  intro n t ht
  exact hrelative (ε n) ⟨(hε n).1.1, (hε n).2.1⟩ (hε n).2.2 t ht

/-- Closed-horizon equality includes time zero only through the explicit
initial-value equalities. A right trace alone does not determine a separately
assigned value of a total-real trajectory at zero.
-/
theorem eq_on_Icc_of_ae_relative_energy
    {V : Type*} [NormedAddCommGroup V]
    {u v : ℝ → V} {g : ℝ → ℝ} {a₀ : V} {T : ℝ} {Good : ℝ → Prop}
    (hT : 0 < T)
    (hg : ContinuousOn g (Ioc (0 : ℝ) T))
    (hg_nonneg : ∀ t ∈ Ioc (0 : ℝ) T, 0 ≤ g t)
    (hg_integrable : IntervalIntegrable g volume (0 : ℝ) T)
    (hprod : IntervalIntegrable
      (fun r => g r * ‖u r - v r‖ ^ 2) volume (0 : ℝ) T)
    (hgood : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) T), Good s)
    (hu_trace : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hv_trace : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hu_zero : u 0 = a₀) (hv_zero : v 0 = a₀)
    (hrelative : ∀ s ∈ Ioo (0 : ℝ) T, Good s →
      ∀ t ∈ Icc s T,
        ‖u t - v t‖ ^ 2 ≤ ‖u s - v s‖ ^ 2 +
          ∫ r in s..t, g r * ‖u r - v r‖ ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have hpositive := eq_on_Ioc_of_ae_relative_energy hT hg hg_nonneg
    hg_integrable hprod hgood hu_trace hv_trace hrelative
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · simpa only [← hzero] using hu_zero.trans hv_zero.symm
  · exact hpositive t ⟨hpos, ht.2⟩

/-- Finite-horizon comparison composes to equality at every nonnegative
time. All coefficient and relative-energy product integrability hypotheses
remain genuine finite-horizon assumptions.
-/
theorem eq_on_nonnegative_of_ae_relative_energy
    {V : Type*} [NormedAddCommGroup V]
    {u v : ℝ → V} {g : ℝ → ℝ} {a₀ : V} {Good : ℝ → Prop}
    (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (hg_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (hg_integrable : ∀ T : ℝ, 0 < T →
      IntervalIntegrable g volume (0 : ℝ) T)
    (hprod : ∀ T : ℝ, 0 < T →
      IntervalIntegrable (fun r => g r * ‖u r - v r‖ ^ 2) volume (0 : ℝ) T)
    (hgood : ∀ T : ℝ, 0 < T →
      ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) T), Good s)
    (hu_trace : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hv_trace : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 a₀))
    (hu_zero : u 0 = a₀) (hv_zero : v 0 = a₀)
    (hrelative : ∀ s : ℝ, 0 < s → Good s → ∀ t : ℝ, s ≤ t →
      ‖u t - v t‖ ^ 2 ≤ ‖u s - v s‖ ^ 2 +
        ∫ r in s..t, g r * ‖u r - v r‖ ^ 2) :
    ∀ t : ℝ, 0 ≤ t → u t = v t := by
  intro t ht
  have hT : 0 < t + 1 := by linarith
  have hlocal := eq_on_Icc_of_ae_relative_energy
    (T := t + 1) hT
    (hg.mono (fun r hr => hr.1))
    (fun r hr => hg_nonneg r hr.1)
    (hg_integrable (t + 1) hT) (hprod (t + 1) hT)
    (hgood (t + 1) hT) hu_trace hv_trace hu_zero hv_zero
    (fun s hs hgs r hr => hrelative s hs.1 hgs r hr.1)
  exact hlocal t ⟨ht, by linarith⟩

/-- The singleton conclusion concerns trajectories on nonnegative time.
Membership of the reference trajectory supplies nonemptiness; pairwise
equality is an explicit premise, supplied by comparison in its application.
No equality of negative-time auxiliary extensions is required or concluded.
-/
theorem restricted_class_eq_singleton_of_eq_on_nonnegative
    {V : Type*} {C : Set (ℝ → V)} {v : ℝ → V}
    (hv : v ∈ C)
    (hEq : ∀ u ∈ C, ∀ t : ℝ, 0 ≤ t → u t = v t) :
    (fun u : ℝ → V => fun t : {t : ℝ // 0 ≤ t} => u t.1) '' C =
      {fun t : {t : ℝ // 0 ≤ t} => v t.1} := by
  ext f
  constructor
  · rintro ⟨u, hu, rfl⟩
    change (fun t : {t : ℝ // 0 ≤ t} => u t.1) =
      (fun t : {t : ℝ // 0 ≤ t} => v t.1)
    funext t
    exact hEq u hu t.1 t.2
  · intro hf
    have hf' : f = (fun t : {t : ℝ // 0 ≤ t} => v t.1) := by
      simpa only [Set.mem_singleton_iff] using hf
    subst f
    exact ⟨v, hv, rfl⟩

end QFA.Assembly.Comparison

end
