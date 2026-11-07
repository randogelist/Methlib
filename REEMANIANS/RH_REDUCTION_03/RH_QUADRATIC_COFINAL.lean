import RH_QUADRATIC_LYAPUNOV

/-!
# Cofinal quadratic-energy admission for the literal Riemann xi

If bounded quadratic Bernstein energy occurs at arbitrarily high degrees,
the already-audited actual-xi Bernstein root limit forces its rate to one,
hence native RiemannHypothesis.

This does NOT construct a terminating finite tail checker or any accepted
actual-xi certificate. No local Lean execution was performed.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RHQuadratic
open RH_HilbertLimit

/-- An unbounded set of degrees with one fixed quadratic bound. -/
def CofinalEnergyBound (K : ℕ) : Prop :=
  ∀ cutoff : ℕ, ∃ n : ℕ, cutoff ≤ n ∧ actualSquareEnergy n ≤ (K : ℝ)

/-- A global linear-growth majorant for fixed natural K. -/
private def affineMajorant (K : ℕ) (n : ℕ) : ℝ :=
  (K : ℝ) + (n : ℝ) + 1

private theorem affineMajorant_one_le (K n : ℕ) :
    1 ≤ affineMajorant K n := by
  unfold affineMajorant
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem affineMajorant_subexponential (K : ℕ) :
    Subexponential (affineMajorant K) := by
  apply subexponential_of_linear_growth
    (affineMajorant K) ((K : ℝ) + 1) 1
    (by positivity) (by norm_num)
  intro n
  change (K : ℝ) + (n : ℝ) + 1 ≤
    ((K : ℝ) + 1) + (1 : ℝ) * (n : ℝ)
  nlinarith

private theorem affineMajorant_root_tendsto_one (K : ℕ) :
    Tendsto (rootScale (affineMajorant K)) atTop (𝓝 1) := by
  have hge : ∀ᶠ n : ℕ in atTop, 1 ≤ affineMajorant K n :=
    Filter.Eventually.of_forall (affineMajorant_one_le K)
  exact (subexponential_iff_rootScale_one hge).mp
    (affineMajorant_subexponential K)

/-- Every certified quadratic-energy hit bounds actual variation at that degree. -/
theorem actualVariation_le_affineMajorant_of_squareEnergy_le
    (K n : ℕ) (h : actualSquareEnergy n ≤ (K : ℝ)) :
    actualVariation n ≤ affineMajorant K n := by
  have hv := rowVariation_le_squareEnergy_add_card actualNormalizedMoment n
  change actualVariation n ≤ actualSquareEnergy n + ((n + 1 : ℕ) : ℝ) at hv
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    push_cast
    ring
  rw [hc] at hv
  unfold affineMajorant
  linarith

/-- Main new implication. A cofinal family of bounded finite checks
    is enough; no all-degree successor estimate is required. -/
theorem nativeRH_of_cofinal_squareEnergy_bound (K : ℕ)
    (h : CofinalEnergyBound K) :
    _root_.RiemannHypothesis := by
  rcases canonical_actual_root_limit_exists with ⟨R, hRge, hroot⟩
  by_cases hRone : R = 1
  · apply canonical_actual_root_one_iff_nativeRH.mp
    simpa [hRone] using hroot
  · have hRgt : 1 < R := lt_of_le_of_ne hRge (Ne.symm hRone)
    let a : ℝ := (1 + R) / 2
    have ha1 : 1 < a := by
      dsimp [a]
      linarith
    have haR : a < R := by
      dsimp [a]
      linarith
    have hlow : ∀ᶠ n : ℕ in atTop, a < rootScale actualVariation n :=
      (tendsto_order.mp hroot).1 a haR
    have hupper : ∀ᶠ n : ℕ in atTop,
        rootScale (affineMajorant K) n < a :=
      (tendsto_order.mp (affineMajorant_root_tendsto_one K)).2 a ha1
    obtain ⟨cutoff, hc⟩ := eventually_atTop.mp (hlow.and hupper)
    obtain ⟨n, hn, hs⟩ := h cutoff
    have hV : actualVariation n ≤ affineMajorant K n :=
      actualVariation_le_affineMajorant_of_squareEnergy_le K n hs
    have hVnonneg : 0 ≤ actualVariation n :=
      rowVariation_nonneg actualNormalizedMoment n
    have hexp : 0 ≤ ((n : ℝ)⁻¹) :=
      inv_nonneg.mpr (Nat.cast_nonneg n)
    have hrootle :
        rootScale actualVariation n ≤ rootScale (affineMajorant K) n := by
      change Real.rpow (actualVariation n) ((n : ℝ)⁻¹) ≤
        Real.rpow (affineMajorant K n) ((n : ℝ)⁻¹)
      exact Real.rpow_le_rpow hVnonneg hV hexp
    obtain ⟨hl, hu⟩ := hc n hn
    linarith

/-- The sharp cofinal quadratic-energy equivalence for the actual xi. -/
theorem cofinal_squareEnergy_iff_nativeRH :
    (∃ K : ℕ, CofinalEnergyBound K) ↔ _root_.RiemannHypothesis := by
  constructor
  · rintro ⟨K, hK⟩
    exact nativeRH_of_cofinal_squareEnergy_bound K hK
  · intro hRH
    refine ⟨1, ?_⟩
    intro cutoff
    exact ⟨cutoff, le_refl _, by
      simpa using actual_squareEnergy_le_one_of_nativeRH hRH cutoff⟩

/-- If RH fails, every fixed quadratic bound eventually fails. -/
theorem eventual_large_squareEnergy_of_not_nativeRH
    (hRH : ¬ _root_.RiemannHypothesis) (K : ℕ) :
    ∃ cutoff : ℕ, ∀ n : ℕ, cutoff ≤ n →
      (K : ℝ) < actualSquareEnergy n := by
  by_contra h
  push Not at h
  have hc : CofinalEnergyBound K := by
    intro cutoff
    obtain ⟨n, hn, hkn⟩ := h cutoff
    exact ⟨n, hn, hkn⟩
  exact hRH (nativeRH_of_cofinal_squareEnergy_bound K hc)

end RHQuadratic
