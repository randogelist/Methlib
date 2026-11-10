import NSE_ROUGH_SHEAR_L2_FAMILY

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter
open scoped BigOperators Topology

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2: directional Fourier-plane L² shear sector.

This is the unconditional coefficient-level proof spine for every fixed
integer direction.  No analytic physical-space NSE conclusion is encoded
in the spectral theorem; the torus-synthesis/Serrin/uniqueness adapter is
separate and explicitly tracked as unresolved.
-/

abbrev Mode3 := Fin 3 → ℤ

/-- Exact integral directional symbol `a · k`. -/
def directionalDot (a k : Mode3) : ℤ :=
  a 0 * k 0 + a 1 * k 1 + a 2 * k 2

/-- Squared physical frequency `(2π)² |k|²` on the unit three-torus. -/
def waveSq (k : Mode3) : ℝ :=
  (2 * Real.pi) ^ 2 *
    (((k 0 : ℝ) ^ 2) + ((k 1 : ℝ) ^ 2) + ((k 2 : ℝ) ^ 2))

theorem waveSq_nonneg (k : Mode3) : 0 ≤ waveSq k := by
  unfold waveSq
  positivity

theorem waveSq_zero : waveSq (0 : Mode3) = 0 := by
  simp [waveSq]

theorem waveSq_neg (k : Mode3) : waveSq (-k) = waveSq k := by
  simp [waveSq]

/-- The coefficient density for the L² norm. -/
def l2Term (a : Mode3 → ℂ) (k : Mode3) : ℝ :=
  ‖a k‖ ^ 2

theorem l2Term_nonneg (a : Mode3 → ℂ) (k : Mode3) :
    0 ≤ l2Term a k := by
  exact sq_nonneg _

/--
Complex Fourier representation of a real, mean-zero scalar profile in
`L²(T³)` with an integer-direction Fourier plane constraint.
The three-dimensional velocity is polarized in `u.direction`.
-/
structure L2DirectionalDatum where
  /-- The directional shear axis is an integer vector, not necessarily primitive. -/
  direction : Mode3
  direction_ne_zero : direction ≠ 0
  /-- Real scalar Fourier coefficients of the `L²₀` profile. -/
  coeff : Mode3 → ℂ
  meanZero : coeff 0 = 0
  reality : ∀ k, coeff (-k) = star (coeff k)
  /-- Distributional directional invariance in exact Fourier coordinates. -/
  planeSupport : ∀ k, directionalDot direction k ≠ 0 → coeff k = 0
  l2Summable : Summable (l2Term coeff)

/-- Heat multiplier for viscosity `ν` and elapsed time `t`. -/
def heatFactor (ν t : ℝ) (k : Mode3) : ℝ :=
  Real.exp (-(ν * t * waveSq k))

theorem heatFactor_pos (ν t : ℝ) (k : Mode3) :
    0 < heatFactor ν t k := by
  unfold heatFactor
  positivity

theorem heatFactor_nonneg (ν t : ℝ) (k : Mode3) :
    0 ≤ heatFactor ν t k :=
  (heatFactor_pos ν t k).le

theorem heatFactor_zero_time (ν : ℝ) (k : Mode3) :
    heatFactor ν 0 k = 1 := by
  simp [heatFactor]

theorem heatFactor_neg (ν t : ℝ) (k : Mode3) :
    heatFactor ν t (-k) = heatFactor ν t k := by
  simp [heatFactor, waveSq_neg]

theorem heatFactor_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : Mode3) :
    heatFactor ν t k ≤ 1 := by
  unfold heatFactor
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ ν * t * waveSq k := by
    exact mul_nonneg (mul_nonneg hν ht) (waveSq_nonneg k)
  linarith

/-- Heat evolution of one scalar shear coefficient. -/
def heatCoeff (ν t : ℝ) (a : Mode3 → ℂ) (k : Mode3) : ℂ :=
  (heatFactor ν t k : ℂ) * a k

theorem heatCoeff_zero_time (ν : ℝ) (a : Mode3 → ℂ) (k : Mode3) :
    heatCoeff ν 0 a k = a k := by
  simp [heatCoeff, heatFactor]

theorem norm_heatCoeff (ν t : ℝ) (a : Mode3 → ℂ) (k : Mode3) :
    ‖heatCoeff ν t a k‖ = heatFactor ν t k * ‖a k‖ := by
  simp [heatCoeff, abs_of_nonneg (heatFactor_nonneg ν t k)]

theorem heatCoeff_norm_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Mode3 → ℂ) (k : Mode3) :
    ‖heatCoeff ν t a k‖ ≤ ‖a k‖ := by
  rw [norm_heatCoeff]
  calc
    heatFactor ν t k * ‖a k‖
        ≤ 1 * ‖a k‖ :=
      mul_le_mul_of_nonneg_right
        (heatFactor_le_one hν ht k) (norm_nonneg _)
    _ = ‖a k‖ := one_mul _

theorem l2Term_heat_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Mode3 → ℂ) (k : Mode3) :
    l2Term (heatCoeff ν t a) k ≤ l2Term a k := by
  unfold l2Term
  rw [norm_heatCoeff]
  have h0 := heatFactor_nonneg ν t k
  have h1 := heatFactor_le_one hν ht k
  have hs : heatFactor ν t k ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (heatFactor ν t k)]
  calc
    (heatFactor ν t k * ‖a k‖) ^ 2
        = heatFactor ν t k ^ 2 * ‖a k‖ ^ 2 := by ring
    _ ≤ 1 * ‖a k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = ‖a k‖ ^ 2 := one_mul _

/-- The heat multiplier preserves the complete real L² directional shear carrier. -/
def heatDatum
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : L2DirectionalDatum) : L2DirectionalDatum where
  direction := u.direction
  direction_ne_zero := u.direction_ne_zero
  coeff := heatCoeff ν t u.coeff
  meanZero := by
    simp [heatCoeff, u.meanZero]
  reality := by
    intro k
    rw [heatCoeff, heatCoeff, heatFactor_neg, u.reality]
    simp
  planeSupport := by
    intro k hk
    simp [heatCoeff, u.planeSupport k hk]
  l2Summable := by
    exact Summable.of_nonneg_of_le
      (fun k => l2Term_nonneg (heatCoeff ν t u.coeff) k)
      (fun k => l2Term_heat_le hν ht u.coeff k)
      u.l2Summable

/-- Homogeneous integer-order Sobolev coefficient density. -/
def smoothTerm (m : ℕ) (a : Mode3 → ℂ) (k : Mode3) : ℝ :=
  waveSq k ^ m * ‖a k‖ ^ 2

theorem smoothTerm_nonneg
    (m : ℕ) (a : Mode3 → ℂ) (k : Mode3) :
    0 ≤ smoothTerm m a k := by
  unfold smoothTerm
  exact mul_nonneg
    (pow_nonneg (waveSq_nonneg k) m)
    (sq_nonneg ‖a k‖)

/-- Elementary exponential domination used for all positive-time derivatives. -/
theorem pow_mul_exp_neg_le_factorial
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x) ≤ (Nat.factorial m : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    positivity
  have h0 := Real.pow_div_factorial_le_exp x hx m
  have h1 : x ^ m ≤ Real.exp x * (Nat.factorial m : ℝ) :=
    (div_le_iff₀ hfac).mp h0
  have h2 :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-x))
  calc
    x ^ m * Real.exp (-x)
        ≤ (Real.exp x * (Nat.factorial m : ℝ)) * Real.exp (-x) := h2
    _ = (Nat.factorial m : ℝ) *
          (Real.exp x * Real.exp (-x)) := by ring
    _ = (Nat.factorial m : ℝ) := by
      rw [← Real.exp_add]
      simp

/-- Uniform multiplier estimate for every positive time. -/
theorem waveSq_pow_heatFactor_sq_le
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (k : Mode3) :
    waveSq k ^ m * heatFactor ν t k ^ 2
      ≤ (Nat.factorial m : ℝ) / (2 * ν * t) ^ m := by
  let c : ℝ := 2 * ν * t
  let x : ℝ := c * waveSq k
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hc.le (waveSq_nonneg k)
  have hmain := pow_mul_exp_neg_le_factorial m hx
  have hheat :
      heatFactor ν t k ^ 2 = Real.exp (-x) := by
    dsimp [x, c]
    rw [heatFactor, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hid :
      x ^ m * Real.exp (-x) =
        c ^ m * (waveSq k ^ m * heatFactor ν t k ^ 2) := by
    rw [hheat]
    dsimp [x]
    rw [mul_pow]
    ring
  have hscaled :
      c ^ m * (waveSq k ^ m * heatFactor ν t k ^ 2)
        ≤ (Nat.factorial m : ℝ) := by
    rw [← hid]
    exact hmain
  have hcp : 0 < c ^ m := pow_pos hc m
  apply (le_div_iff₀ hcp).2
  simpa [c, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem smoothTerm_heat_le
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (a : Mode3 → ℂ) (k : Mode3) :
    smoothTerm m (heatCoeff ν t a) k
      ≤ ((Nat.factorial m : ℝ) / (2 * ν * t) ^ m) * l2Term a k := by
  unfold smoothTerm l2Term
  rw [norm_heatCoeff]
  calc
    waveSq k ^ m * (heatFactor ν t k * ‖a k‖) ^ 2
        = (waveSq k ^ m * heatFactor ν t k ^ 2) * ‖a k‖ ^ 2 := by
            ring
    _ ≤ ((Nat.factorial m : ℝ) / (2 * ν * t) ^ m) * ‖a k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (waveSq_pow_heatFactor_sq_le hν ht m k)
        (sq_nonneg _)

/-- Every L² directional shear is in every integer Sobolev class at every positive time. -/
theorem positive_time_smoothing
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (u : L2DirectionalDatum) :
    Summable (smoothTerm m (heatCoeff ν t u.coeff)) := by
  let C : ℝ := (Nat.factorial m : ℝ) / (2 * ν * t) ^ m
  exact Summable.of_nonneg_of_le
    (fun k => smoothTerm_nonneg m (heatCoeff ν t u.coeff) k)
    (fun k => by
      simpa [C] using smoothTerm_heat_le hν ht m u.coeff k)
    (u.l2Summable.mul_left C)

/-- Squared coefficient error relative to the initial profile. -/
def traceErrorTerm
    (ν t : ℝ) (a : Mode3 → ℂ) (k : Mode3) : ℝ :=
  ‖heatCoeff ν t a k - a k‖ ^ 2

theorem traceErrorTerm_nonneg
    (ν t : ℝ) (a : Mode3 → ℂ) (k : Mode3) :
    0 ≤ traceErrorTerm ν t a k := by
  exact sq_nonneg _

theorem traceErrorTerm_le_four
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Mode3 → ℂ) (k : Mode3) :
    traceErrorTerm ν t a k ≤ 4 * l2Term a k := by
  have hdiff :
      ‖heatCoeff ν t a k - a k‖ ≤ 2 * ‖a k‖ := by
    calc
      ‖heatCoeff ν t a k - a k‖
          ≤ ‖heatCoeff ν t a k‖ + ‖a k‖ := norm_sub_le _ _
      _ ≤ ‖a k‖ + ‖a k‖ := by
        exact add_le_add (heatCoeff_norm_le hν ht a k) le_rfl
      _ = 2 * ‖a k‖ := by ring
  have hsq :
      ‖heatCoeff ν t a k - a k‖ ^ 2
        ≤ (2 * ‖a k‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _))).2 hdiff
  calc
    traceErrorTerm ν t a k
        = ‖heatCoeff ν t a k - a k‖ ^ 2 := rfl
    _ ≤ (2 * ‖a k‖) ^ 2 := hsq
    _ = 4 * l2Term a k := by
      unfold l2Term
      ring

theorem traceErrorTerm_tendsto_zero
    (ν : ℝ) (a : Mode3 → ℂ) (k : Mode3) :
    Tendsto (fun t : ℝ => traceErrorTerm ν t a k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc :
      ContinuousAt (fun t : ℝ => traceErrorTerm ν t a k) 0 := by
    unfold traceErrorTerm heatCoeff heatFactor
    fun_prop
  have hw :
      ContinuousWithinAt (fun t : ℝ => traceErrorTerm ν t a k)
        (Set.Ioi 0) 0 :=
    hc.continuousWithinAt
  simpa [traceErrorTerm, heatCoeff, heatFactor] using hw.tendsto

/-- Squared L² trace error, represented exactly by Parseval coefficients. -/
def traceErrorSq (ν t : ℝ) (a : Mode3 → ℂ) : ℝ :=
  ∑' k, traceErrorTerm ν t a k

/-- Strong L² convergence of the heat orbit to its input trace. -/
theorem traceErrorSq_tendsto_zero
    {ν : ℝ} (hν : 0 < ν) (u : L2DirectionalDatum) :
    Tendsto (fun t : ℝ => traceErrorSq ν t u.coeff)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsum :
      Summable (fun k => 4 * l2Term u.coeff k) :=
    u.l2Summable.mul_left 4
  have hpoint :
      ∀ k, Tendsto
        (fun t : ℝ => traceErrorTerm ν t u.coeff k)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    intro k
    exact traceErrorTerm_tendsto_zero ν u.coeff k
  have hbound :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k,
        ‖traceErrorTerm ν t u.coeff k‖
          ≤ 4 * l2Term u.coeff k := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    intro k
    rw [Real.norm_eq_abs,
      abs_of_nonneg (traceErrorTerm_nonneg ν t u.coeff k)]
    exact traceErrorTerm_le_four hν.le ht.le u.coeff k
  have h :=
    tendsto_tsum_of_dominated_convergence
      (f := fun t k => traceErrorTerm ν t u.coeff k)
      (g := fun _ => (0 : ℝ))
      (bound := fun k => 4 * l2Term u.coeff k)
      hsum hpoint hbound
  simpa [traceErrorSq] using h


/-! ## Three-dimensional directional spectral nonlinearity

The exact Fourier velocity is `a_i * scalarCoeff(k)`. The multiplier
`2πik_j` gives the actual Fourier derivative, and therefore the
advection coefficient is the convolution of the stated finite kernel.
Its cancellation is proved from `directionalDot a k = 0` on the support.
-/

def velocityCoeff
    (ν t : ℝ) (u : L2DirectionalDatum)
    (k : Mode3) (i : Fin 3) : ℂ :=
  (u.direction i : ℂ) * heatCoeff ν t u.coeff k

def derivativeSymbol (k : Mode3) (i : Fin 3) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * (k i : ℂ)

def advectiveScalar
    (ν t : ℝ) (u : L2DirectionalDatum)
    (p q : Mode3) : ℂ :=
  ∑ j : Fin 3, velocityCoeff ν t u p j * derivativeSymbol q j

/-- The standard Fourier advection contraction factors through `a · q`. -/
theorem advectiveScalar_factor
    (ν t : ℝ) (u : L2DirectionalDatum)
    (p q : Mode3) :
    advectiveScalar ν t u p q =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        (directionalDot u.direction q : ℂ) *
          heatCoeff ν t u.coeff p := by
  simp only [advectiveScalar, velocityCoeff, derivativeSymbol,
    Fin.sum_univ_three, directionalDot]
  push_cast
  ring

/-- The nonlinear convolution integrand is identically zero. -/
theorem nonlinearKernel_zero
    (ν t : ℝ) (u : L2DirectionalDatum)
    (p q : Mode3) (i : Fin 3) :
    advectiveScalar ν t u p q * velocityCoeff ν t u q i = 0 := by
  by_cases hd : directionalDot u.direction q = 0
  · rw [advectiveScalar_factor]
    simp [hd]
  · simp [velocityCoeff, heatCoeff, u.planeSupport q hd]

/-- Each Fourier divergence coefficient of the directional heat orbit is zero. -/
def divergenceCoeff
    (ν t : ℝ) (u : L2DirectionalDatum) (k : Mode3) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol k j * velocityCoeff ν t u k j

theorem divergenceCoeff_eq_advectiveScalar
    (ν t : ℝ) (u : L2DirectionalDatum) (k : Mode3) :
    divergenceCoeff ν t u k = advectiveScalar ν t u k k := by
  simp only [divergenceCoeff, advectiveScalar, Fin.sum_univ_three]
  ring

@[simp] theorem divergenceCoeff_zero
    (ν t : ℝ) (u : L2DirectionalDatum) (k : Mode3) :
    divergenceCoeff ν t u k = 0 := by
  by_cases hd : directionalDot u.direction k = 0
  · rw [divergenceCoeff_eq_advectiveScalar, advectiveScalar_factor]
    simp [hd]
  · simp [divergenceCoeff, velocityCoeff, heatCoeff, u.planeSupport k hd]

/-- Finite, genuinely factored Fourier coefficient of `(u · ∇)u`. -/
def rawConvectionCoeff
    (S : Finset Mode3) (ν t : ℝ) (u : L2DirectionalDatum)
    (k : Mode3) (i : Fin 3) : ℂ :=
  ∑ p ∈ S,
    advectiveScalar ν t u p (k - p) *
      velocityCoeff ν t u (k - p) i

@[simp] theorem rawConvectionCoeff_zero
    (S : Finset Mode3) (ν t : ℝ) (u : L2DirectionalDatum)
    (k : Mode3) (i : Fin 3) :
    rawConvectionCoeff S ν t u k i = 0 := by
  simp [rawConvectionCoeff, nonlinearKernel_zero]

/-- Exact heat-multiplier scalar coefficient ODE. -/
theorem heatFactor_hasDerivAt
    (ν t : ℝ) (k : Mode3) :
    HasDerivAt (fun s : ℝ => heatFactor ν s k)
      (-(ν * waveSq k) * heatFactor ν t k) t := by
  have hinner :
      HasDerivAt
        (fun s : ℝ => -(ν * s * waveSq k))
        (-(ν * waveSq k)) t :=
    ((hasDerivAt_const_mul (x := t) ν).mul_const (waveSq k)).neg
  simpa only [heatFactor, mul_comm] using hinner.exp

/-- Every directional datum possesses the unconditional spectral flow. -/
structure DirectionalSpectralFlow
    (ν : ℝ) (u : L2DirectionalDatum) : Prop where
  initialCoefficient :
    ∀ k, heatCoeff ν 0 u.coeff k = u.coeff k
  strongL2Trace :
    Tendsto (fun t : ℝ => traceErrorSq ν t u.coeff)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
  allPositiveSobolevOrders :
    ∀ (t : ℝ), 0 < t → ∀ m : ℕ,
      Summable (smoothTerm m (heatCoeff ν t u.coeff))
  divergenceFree :
    ∀ (t : ℝ) (k : Mode3), divergenceCoeff ν t u k = 0
  convectionZero :
    ∀ (S : Finset Mode3) (t : ℝ) (k : Mode3) (i : Fin 3),
      rawConvectionCoeff S ν t u k i = 0
  heatODE :
    ∀ (t : ℝ) (k : Mode3),
      HasDerivAt (fun s : ℝ => heatFactor ν s k)
        (-(ν * waveSq k) * heatFactor ν t k) t
  directionalInvariance :
    ∀ (t : ℝ), 0 ≤ t → ∀ k,
      directionalDot u.direction k ≠ 0 →
        heatCoeff ν t u.coeff k = 0

/-- Universal unconditional directional `L²` Fourier regularity. -/
theorem S_DIR_L2_SPECTRAL_REGULARITY
    (ν : ℝ) (hν : 0 < ν) (u : L2DirectionalDatum) :
    DirectionalSpectralFlow ν u := by
  refine
    { initialCoefficient := ?_
      strongL2Trace := traceErrorSq_tendsto_zero hν u
      allPositiveSobolevOrders := ?_
      divergenceFree := ?_
      convectionZero := ?_
      heatODE := ?_
      directionalInvariance := ?_ }
  · intro k
    exact heatCoeff_zero_time ν u.coeff k
  · intro t ht m
    exact positive_time_smoothing hν ht m u
  · intro t k
    exact divergenceCoeff_zero ν t u k
  · intro S t k i
    exact rawConvectionCoeff_zero S ν t u k i
  · intro t k
    exact heatFactor_hasDerivAt ν t k
  · intro t ht k hk
    simp [heatCoeff, u.planeSupport k hk]

/-! ## Exact finite Fourier-flux M7 cancellation -/

/-- Finite Fourier energy flux measured against the exact nonlinear coefficient. -/
def FourierFlux
    (S : Finset Mode3) (ν t : ℝ) (u : L2DirectionalDatum) : ℝ :=
  ∑ k ∈ S, ∑ i : Fin 3,
    (star (velocityCoeff ν t u k i) *
      rawConvectionCoeff S ν t u k i).re

/-- No nonlinear Fourier flux is present on any finite spectral cutoff. -/
theorem S_DIR_L2_M7_FOURIER_FLUX_ZERO
    (S : Finset Mode3) (ν t : ℝ) (u : L2DirectionalDatum) :
    FourierFlux S ν t u = 0 := by
  simp [FourierFlux]

/-- Finite positive-part M7 density, with the totalized `0/0=0` convention. -/
def FourierM7Density
    (cuts : ℕ → Finset Mode3) (levels : Finset ℕ)
    (weights capacities : ℕ → ℝ)
    (ν t : ℝ) (u : L2DirectionalDatum) : ℝ :=
  ∑ N ∈ levels,
    weights N *
      (max (FourierFlux (cuts N) ν t u) 0) ^ 2 / capacities N

/-- Any choice of finite levels, weights and capacities gives zero flux action. -/
theorem S_DIR_L2_M7_FOURIER_DENSITY_ZERO
    (cuts : ℕ → Finset Mode3) (levels : Finset ℕ)
    (weights capacities : ℕ → ℝ)
    (ν t : ℝ) (u : L2DirectionalDatum) :
    FourierM7Density cuts levels weights capacities ν t u = 0 := by
  simp [FourierM7Density, S_DIR_L2_M7_FOURIER_FLUX_ZERO]

end SDirL2
