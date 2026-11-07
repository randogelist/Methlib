import RH_HilbertLimit.AnalyticClosure
import Mathlib.Tactic

/-!
# Actual-xi quadratic Bernstein Lyapunov criterion

The source of `actualNormalizedMoment` is the literal AWPIRH theta/xi
carrier imported from the previously audited cached HVR development.
No hypothesis is silently postulated about its zeros.

The root results are unconditional equivalences and conditional one-step
transfers. They do NOT establish an accepted finite witness or RH.

Prepared for external Lean 4.33.0 cached compilation only.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RHQuadratic
open RH_HilbertLimit

/-- Unnormalized quadratic Bernstein-row energy of a real moment sequence. -/
def squareEnergy (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (bernsteinWeight u n j) ^ 2

/-- The actual Riemann xi carrier, not a free sequence supplied by a witness. -/
def actualSquareEnergy (n : ℕ) : ℝ :=
  squareEnergy actualNormalizedMoment n

private theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    nlinarith [sq_nonneg (x + (1 / 2 : ℝ))]

theorem squareEnergy_nonneg (u : ℕ → ℝ) (n : ℕ) :
    0 ≤ squareEnergy u n := by
  unfold squareEnergy
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (bernsteinWeight u n j))

theorem actualSquareEnergy_nonneg (n : ℕ) :
    0 ≤ actualSquareEnergy n :=
  squareEnergy_nonneg actualNormalizedMoment n

/-- A quadratic-to-linear transfer requiring no Cauchy-Schwarz lemma. -/
theorem rowVariation_le_squareEnergy_add_card
    (u : ℕ → ℝ) (n : ℕ) :
    rowVariation u n ≤ squareEnergy u n + ((n + 1 : ℕ) : ℝ) := by
  unfold rowVariation
  calc
    (∑ j ∈ Finset.range (n + 1), |bernsteinWeight u n j|) ≤
        ∑ j ∈ Finset.range (n + 1),
          ((bernsteinWeight u n j) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := abs_le_one_add_sq (bernsteinWeight u n j)
      linarith
    _ = squareEnergy u n + ((n + 1 : ℕ) : ℝ) := by
      simp [squareEnergy, Finset.sum_add_distrib]

/-- An explicit linear majorant supplies the audited Subexponential type. -/
theorem subexponential_of_linear_growth
    (V : ℕ → ℝ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, V n ≤ C + D * (n : ℝ)) :
    Subexponential V := by
  intro ε hε
  let M : ℝ := C + D / ε + 1
  have hdiv : 0 ≤ D / ε := div_nonneg hD hε.le
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨M, hM, ?_⟩
  intro n
  have hCM : C ≤ M := by dsimp [M]; linarith
  have hDM : D ≤ M * ε := by
    have hd : D / ε ≤ M := by dsimp [M]; linarith
    exact (div_le_iff₀ hε).mp hd
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he : 1 + ε * (n : ℝ) ≤ Real.exp (ε * (n : ℝ)) := by
    simpa only [add_comm] using (Real.add_one_le_exp (ε * (n : ℝ)))
  calc
    V n ≤ C + D * (n : ℝ) := h n
    _ ≤ M + (M * ε) * (n : ℝ) :=
      add_le_add hCM (mul_le_mul_of_nonneg_right hDM hn)
    _ = M * (1 + ε * (n : ℝ)) := by ring
    _ ≤ M * Real.exp (ε * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left he hM.le

/-- Uniform quadratic-energy bound implies subexponential actual variation. -/
theorem actual_subexponential_of_uniform_squareEnergy (K : ℕ)
    (hK : ∀ n : ℕ, actualSquareEnergy n ≤ (K : ℝ)) :
    Subexponential actualVariation := by
  apply subexponential_of_linear_growth
    actualVariation ((K : ℝ) + 1) 1 (by positivity) (by norm_num)
  intro n
  have hv := rowVariation_le_squareEnergy_add_card actualNormalizedMoment n
  have hs := hK n
  have hc : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  rw [hc] at hv
  change squareEnergy actualNormalizedMoment n ≤ (K : ℝ) at hs
  change rowVariation actualNormalizedMoment n ≤
    ((K : ℝ) + 1) + (1 : ℝ) * (n : ℝ)
  linarith

/-- Actual-xi semantic root: no free spectral calibration or witness checker. -/
theorem nativeRH_of_uniform_squareEnergy (K : ℕ)
    (hK : ∀ n : ℕ, actualSquareEnergy n ≤ (K : ℝ)) :
    _root_.RiemannHypothesis :=
  canonical_actual_subexponential_iff_nativeRH.mp
    (actual_subexponential_of_uniform_squareEnergy K hK)

/-- The normalized actual row has total mass exactly one. -/
theorem actual_row_mass_one (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), actualWeight n j) = 1 := by
  simpa only [actualWeight] using
    (sum_bernsteinWeight_eq_one actualNormalizedMoment
      (actualNormalizedMoment_zero (ne_of_gt actualKappa_pos)) n)

/-- RH gives the quadratic unit bound by positivity and mass one. -/
theorem actual_squareEnergy_le_one_of_nativeRH
    (hRH : _root_.RiemannHypothesis) (n : ℕ) :
    actualSquareEnergy n ≤ 1 := by
  let s : Finset ℕ := Finset.range (n + 1)
  have hp : ∀ j ∈ s, 0 ≤ actualWeight n j := by
    intro j hj
    have hjle : j ≤ n := by
      have hlt := Finset.mem_range.mp hj
      omega
    exact (canonical_actual_weights_nonnegative_iff_nativeRH.mpr hRH) n j hjle
  have hm : (∑ j ∈ s, actualWeight n j) = 1 := by
    simpa only [s] using actual_row_mass_one n
  have hterm : ∀ j ∈ s, (actualWeight n j) ^ 2 ≤ actualWeight n j := by
    intro j hj
    have h0 := hp j hj
    have hsingle : actualWeight n j ≤ ∑ k ∈ s, actualWeight n k :=
      Finset.single_le_sum (fun k hk => hp k hk) hj
    have h1 : actualWeight n j ≤ 1 := by
      rw [hm] at hsingle
      exact hsingle
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  calc
    actualSquareEnergy n = ∑ j ∈ s, (actualWeight n j) ^ 2 := rfl
    _ ≤ ∑ j ∈ s, actualWeight n j :=
      Finset.sum_le_sum (fun j hj => hterm j hj)
    _ = 1 := hm

/-- Exact actual-xi quadratic all-row criterion. -/
theorem actual_squareEnergy_le_one_iff_nativeRH :
    (∀ n : ℕ, actualSquareEnergy n ≤ 1) ↔ _root_.RiemannHypothesis := by
  constructor
  · intro h
    apply nativeRH_of_uniform_squareEnergy 1
    intro n
    simpa using h n
  · exact actual_squareEnergy_le_one_of_nativeRH

/-- Finite numerical parameter, with universal (non-computable) admissibility. -/
theorem actual_exists_uniform_squareEnergy_iff_nativeRH :
    (∃ K : ℕ, ∀ n : ℕ, actualSquareEnergy n ≤ (K : ℝ)) ↔
      _root_.RiemannHypothesis := by
  constructor
  · rintro ⟨K, hK⟩
    exact nativeRH_of_uniform_squareEnergy K hK
  · intro hRH
    exact ⟨1, by intro n; simpa using actual_squareEnergy_le_one_of_nativeRH hRH n⟩

@[simp] theorem actual_squareEnergy_zero : actualSquareEnergy 0 = 1 := by
  simp [actualSquareEnergy, squareEnergy, bernsteinWeight_zero_zero,
    actualNormalizedMoment_zero (ne_of_gt actualKappa_pos)]

/-- A fixed unit additive step grows the energy at most linearly. -/
theorem quadratic_linear_of_unit_steps
    (S : ℕ → ℝ) (h0 : S 0 ≤ 1)
    (hstep : ∀ n : ℕ, S (n + 1) ≤ S n + 1) :
    ∀ n : ℕ, S n ≤ (n : ℝ) + 1 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
      have hs := hstep n
      have hc : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        push_cast
        ring
      rw [hc]
      linarith

/-- Every universal unit quadratic step proves the literal Riemann hypothesis. -/
theorem nativeRH_of_quadratic_unit_steps
    (hstep : ∀ n : ℕ,
      actualSquareEnergy (n + 1) ≤ actualSquareEnergy n + 1) :
    _root_.RiemannHypothesis := by
  have hlinear : ∀ n : ℕ, actualSquareEnergy n ≤ (n : ℝ) + 1 :=
    quadratic_linear_of_unit_steps actualSquareEnergy
      (by simp) hstep
  apply canonical_actual_subexponential_iff_nativeRH.mp
  apply subexponential_of_linear_growth actualVariation 2 2
    (by norm_num) (by norm_num)
  intro n
  have hv := rowVariation_le_squareEnergy_add_card actualNormalizedMoment n
  have hs := hlinear n
  have hc : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  rw [hc] at hv
  change squareEnergy actualNormalizedMoment n ≤ (n : ℝ) + 1 at hs
  change rowVariation actualNormalizedMoment n ≤
    (2 : ℝ) + 2 * (n : ℝ)
  linarith

/-- A nonzero fixed step budget is RH-equivalent for the actual xi carrier. -/
theorem actual_quadratic_unit_steps_iff_nativeRH :
    (∀ n : ℕ,
      actualSquareEnergy (n + 1) ≤ actualSquareEnergy n + 1) ↔
      _root_.RiemannHypothesis := by
  constructor
  · exact nativeRH_of_quadratic_unit_steps
  · intro hRH n
    have hn := actual_squareEnergy_le_one_of_nativeRH hRH (n + 1)
    have hn0 := actualSquareEnergy_nonneg n
    linarith

/-- The stronger scalar Lyapunov monotonicity also suffices for RH. -/
theorem nativeRH_of_quadratic_monotone
    (h : ∀ n : ℕ, actualSquareEnergy (n + 1) ≤ actualSquareEnergy n) :
    _root_.RiemannHypothesis := by
  apply nativeRH_of_quadratic_unit_steps
  intro n
  have hn := h n
  linarith

/-! ## Exact one-new-moment quadratic successor algebra -/

/-- The row contribution independent of the new moment `u q`. -/
def prefixWeight (u : ℕ → ℝ) (q j : ℕ) : ℝ :=
  (Nat.choose q j : ℝ) *
    ∑ r ∈ Finset.range (q - j),
      (-1 : ℝ) ^ r * (Nat.choose (q - j) r : ℝ) * u (j + r)

/-- The coefficient of the sole new moment `u q`. -/
def lastCoeff (q j : ℕ) : ℝ :=
  (Nat.choose q j : ℝ) * (-1 : ℝ) ^ (q - j)

/-- Finite identity, with no analytic or RH assumptions. -/
theorem bernsteinWeight_prefix_decompose (u : ℕ → ℝ) (q j : ℕ)
    (hj : j ≤ q) :
    bernsteinWeight u q j = prefixWeight u q j + lastCoeff q j * u q := by
  unfold bernsteinWeight prefixWeight lastCoeff
  rw [Finset.sum_range_succ]
  have hidx : j + (q - j) = q := Nat.add_sub_of_le hj
  rw [hidx, Nat.choose_self]
  ring

def quadA (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1), (lastCoeff q j) ^ 2

def quadB (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1), lastCoeff q j * prefixWeight u q j

def quadC (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1), (prefixWeight u q j) ^ 2

/-- The leading quadratic coefficient is strictly positive in every degree. -/
theorem quadA_pos (q : ℕ) : 0 < quadA q := by
  have hle : (lastCoeff q q) ^ 2 ≤ quadA q := by
    unfold quadA
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (lastCoeff q j)) (by simp)
  have heq : lastCoeff q q = 1 := by simp [lastCoeff]
  rw [heq] at hle
  nlinarith

/-- Exact quadratic expansion in the single new actual moment. -/
theorem squareEnergy_polynomial (u : ℕ → ℝ) (q : ℕ) :
    squareEnergy u q =
      quadA q * (u q) ^ 2 + 2 * quadB u q * u q + quadC u q := by
  unfold squareEnergy
  calc
    (∑ j ∈ Finset.range (q + 1), (bernsteinWeight u q j) ^ 2) =
        ∑ j ∈ Finset.range (q + 1),
          (prefixWeight u q j + lastCoeff q j * u q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [bernsteinWeight_prefix_decompose u q j (by
        have hlt := Finset.mem_range.mp hj
        omega)]
    _ = ∑ j ∈ Finset.range (q + 1),
          ((lastCoeff q j) ^ 2 * (u q) ^ 2 +
             2 * (lastCoeff q j * prefixWeight u q j) * u q +
             (prefixWeight u q j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = quadA q * (u q) ^ 2 + 2 * quadB u q * u q + quadC u q := by
      unfold quadA quadB quadC
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Prefix-only scalar threshold for the one-step squared inequality. -/
def quadR (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  quadA q * (squareEnergy u (q - 1) - quadC u q) + (quadB u q) ^ 2

private theorem completed_square_identity (u : ℕ → ℝ) (q : ℕ) :
    quadA q * squareEnergy u q =
      (quadA q * u q + quadB u q) ^ 2 +
      quadA q * quadC u q - (quadB u q) ^ 2 := by
  rw [squareEnergy_polynomial]
  ring

/-- Exact scalar square inequality for a fixed unit successor budget. -/
theorem quadratic_unit_step_iff_scalar_square (u : ℕ → ℝ) (q : ℕ) :
    squareEnergy u q ≤ squareEnergy u (q - 1) + 1 ↔
      (quadA q * u q + quadB u q) ^ 2 ≤ quadR u q + quadA q := by
  have hA := quadA_pos q
  have heq := completed_square_identity u q
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hA.le
    unfold quadR
    nlinarith [heq]
  · intro h
    have hmul : quadA q * squareEnergy u q ≤
        quadA q * (squareEnergy u (q - 1) + 1) := by
      unfold quadR at h
      nlinarith [heq]
    exact (mul_le_mul_iff_of_pos_left hA).mp hmul

/-- The zero-budget monotonicity test has the same square-completion. -/
theorem quadratic_monotone_step_iff_scalar_square (u : ℕ → ℝ) (q : ℕ) :
    squareEnergy u q ≤ squareEnergy u (q - 1) ↔
      (quadA q * u q + quadB u q) ^ 2 ≤ quadR u q := by
  have hA := quadA_pos q
  have heq := completed_square_identity u q
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hA.le
    unfold quadR
    nlinarith [heq]
  · intro h
    have hmul : quadA q * squareEnergy u q ≤
        quadA q * squareEnergy u (q - 1) := by
      unfold quadR at h
      nlinarith [heq]
    exact (mul_le_mul_iff_of_pos_left hA).mp hmul

/-- Every actual-xi scalar unit successor gate implies RH. -/
theorem nativeRH_of_all_actual_scalar_gates
    (h : ∀ q : ℕ,
      (quadA q * actualNormalizedMoment q + quadB actualNormalizedMoment q) ^ 2 ≤
        quadR actualNormalizedMoment q + quadA q) :
    _root_.RiemannHypothesis := by
  apply nativeRH_of_quadratic_unit_steps
  intro n
  have hg := (quadratic_unit_step_iff_scalar_square
    actualNormalizedMoment (n + 1)).mpr (h (n + 1))
  change actualSquareEnergy (n + 1) ≤ actualSquareEnergy n + 1 at hg
  exact hg

/-- Exact equivalence with the actual-xi all-degree one-square gates. -/
theorem actual_all_scalar_gates_iff_nativeRH :
    (∀ q : ℕ,
      (quadA q * actualNormalizedMoment q + quadB actualNormalizedMoment q) ^ 2 ≤
        quadR actualNormalizedMoment q + quadA q) ↔
      _root_.RiemannHypothesis := by
  constructor
  · exact nativeRH_of_all_actual_scalar_gates
  · intro hRH q
    apply (quadratic_unit_step_iff_scalar_square actualNormalizedMoment q).mp
    have hunit := actual_squareEnergy_le_one_of_nativeRH hRH q
    have hnon := actualSquareEnergy_nonneg (q - 1)
    change squareEnergy actualNormalizedMoment q ≤ 1 at hunit
    change 0 ≤ squareEnergy actualNormalizedMoment (q - 1) at hnon
    change squareEnergy actualNormalizedMoment q ≤
      squareEnergy actualNormalizedMoment (q - 1) + 1
    linarith

/-! ## Finite source algebra and rational arithmetic admission -/

/-- The prefix predictor uses no `u q` and no `beta (q+1)`. -/
def prefixPredictor (u beta : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ r ∈ Finset.range q,
    (-1 : ℝ) ^ r * beta (r + 1) * u (q - (r + 1))

/-- A visible source identity, not a theorem about actual xi yet. -/
def SourceStep (u beta : ℕ → ℝ) (q : ℕ) : Prop :=
  u q = prefixPredictor u beta q +
    (-1 : ℝ) ^ q * ((q + 1 : ℕ) : ℝ) * beta (q + 1)

/-- One-coefficient Taylor substitution in the exact quadratic gate. -/
theorem source_quadratic_gate_iff (u beta : ℕ → ℝ) (q : ℕ)
    (hs : SourceStep u beta q) :
    squareEnergy u q ≤ squareEnergy u (q - 1) + 1 ↔
      (quadA q * (prefixPredictor u beta q +
          (-1 : ℝ) ^ q * ((q + 1 : ℕ) : ℝ) * beta (q + 1)) +
        quadB u q) ^ 2 ≤ quadR u q + quadA q := by
  rw [quadratic_unit_step_iff_scalar_square]
  rw [show u q = prefixPredictor u beta q +
    (-1 : ℝ) ^ q * ((q + 1 : ℕ) : ℝ) * beta (q + 1) from hs]

/-- Concrete one-step rational checker. It checks arithmetic, not xi-source validity. -/
def checkRationalSquareGate (A B R x : ℚ) : Bool :=
  decide ((A * x + B) ^ 2 ≤ R + A)

theorem checkRationalSquareGate_sound (A B R x : ℚ)
    (h : checkRationalSquareGate A B R x = true) :
    (A * x + B) ^ 2 ≤ R + A := by
  simpa only [checkRationalSquareGate, decide_eq_true_eq] using h

end RHQuadratic
