import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter
open scoped BigOperators Topology

noncomputable section

namespace NSERoughShearL2Family

/-
The coefficient carrier is the real-valued mean-zero L² shear sector,
represented by complex Fourier coefficients on T² with conjugation symmetry.
The corresponding three-dimensional velocity has the form
    u(x₁,x₂,x₃,t) = (V(x₂,x₃,t), 0, 0).
-/

abbrev Mode2 := Fin 2 → ℤ

/-- Squared physical frequency `(2π)² |k|²` on the unit two-torus. -/
def freqSq (k : Mode2) : ℝ :=
  (2 * Real.pi) ^ 2 *
    (((k 0 : ℝ) ^ 2) + ((k 1 : ℝ) ^ 2))

theorem freqSq_nonneg (k : Mode2) : 0 ≤ freqSq k := by
  unfold freqSq
  positivity

theorem freqSq_zero : freqSq (0 : Mode2) = 0 := by
  simp [freqSq]

theorem freqSq_neg (k : Mode2) : freqSq (-k) = freqSq k := by
  simp [freqSq]

/-- The coefficient density for the L² norm. -/
def l2Term (a : Mode2 → ℂ) (k : Mode2) : ℝ :=
  ‖a k‖ ^ 2

theorem l2Term_nonneg (a : Mode2 → ℂ) (k : Mode2) :
    0 ≤ l2Term a k := by
  exact sq_nonneg _

/--
Complex Fourier representation of a real, mean-zero scalar profile in
`L²(T²)`.  The three-dimensional velocity is obtained by first-coordinate
polarization.
-/
structure L2ShearDatum where
  coeff : Mode2 → ℂ
  meanZero : coeff 0 = 0
  reality : ∀ k, coeff (-k) = star (coeff k)
  l2Summable : Summable (l2Term coeff)

/-- Heat multiplier for viscosity `ν` and elapsed time `t`. -/
def heatFactor (ν t : ℝ) (k : Mode2) : ℝ :=
  Real.exp (-(ν * t * freqSq k))

theorem heatFactor_pos (ν t : ℝ) (k : Mode2) :
    0 < heatFactor ν t k := by
  unfold heatFactor
  positivity

theorem heatFactor_nonneg (ν t : ℝ) (k : Mode2) :
    0 ≤ heatFactor ν t k :=
  (heatFactor_pos ν t k).le

theorem heatFactor_zero_time (ν : ℝ) (k : Mode2) :
    heatFactor ν 0 k = 1 := by
  simp [heatFactor]

theorem heatFactor_neg (ν t : ℝ) (k : Mode2) :
    heatFactor ν t (-k) = heatFactor ν t k := by
  simp [heatFactor, freqSq_neg]

theorem heatFactor_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : Mode2) :
    heatFactor ν t k ≤ 1 := by
  unfold heatFactor
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ ν * t * freqSq k := by
    exact mul_nonneg (mul_nonneg hν ht) (freqSq_nonneg k)
  linarith

/-- Heat evolution of one scalar shear coefficient. -/
def heatCoeff (ν t : ℝ) (a : Mode2 → ℂ) (k : Mode2) : ℂ :=
  (heatFactor ν t k : ℂ) * a k

theorem heatCoeff_zero_time (ν : ℝ) (a : Mode2 → ℂ) (k : Mode2) :
    heatCoeff ν 0 a k = a k := by
  simp [heatCoeff, heatFactor]

theorem norm_heatCoeff (ν t : ℝ) (a : Mode2 → ℂ) (k : Mode2) :
    ‖heatCoeff ν t a k‖ = heatFactor ν t k * ‖a k‖ := by
  simp [heatCoeff, abs_of_nonneg (heatFactor_nonneg ν t k)]

theorem heatCoeff_norm_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Mode2 → ℂ) (k : Mode2) :
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
    (a : Mode2 → ℂ) (k : Mode2) :
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

/-- The heat multiplier preserves the complete real L² shear carrier. -/
def heatDatum
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : L2ShearDatum) : L2ShearDatum where
  coeff := heatCoeff ν t u.coeff
  meanZero := by
    simp [heatCoeff, u.meanZero]
  reality := by
    intro k
    rw [heatCoeff, heatCoeff, heatFactor_neg, u.reality]
    simp
  l2Summable := by
    exact Summable.of_nonneg_of_le
      (fun k => l2Term_nonneg (heatCoeff ν t u.coeff) k)
      (fun k => l2Term_heat_le hν ht u.coeff k)
      u.l2Summable

/-- Homogeneous integer-order Sobolev coefficient density. -/
def smoothTerm (m : ℕ) (a : Mode2 → ℂ) (k : Mode2) : ℝ :=
  freqSq k ^ m * ‖a k‖ ^ 2

theorem smoothTerm_nonneg
    (m : ℕ) (a : Mode2 → ℂ) (k : Mode2) :
    0 ≤ smoothTerm m a k := by
  unfold smoothTerm
  exact mul_nonneg
    (pow_nonneg (freqSq_nonneg k) m)
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
theorem freqSq_pow_heatFactor_sq_le
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (k : Mode2) :
    freqSq k ^ m * heatFactor ν t k ^ 2
      ≤ (Nat.factorial m : ℝ) / (2 * ν * t) ^ m := by
  let c : ℝ := 2 * ν * t
  let x : ℝ := c * freqSq k
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hc.le (freqSq_nonneg k)
  have hmain := pow_mul_exp_neg_le_factorial m hx
  have hheat :
      heatFactor ν t k ^ 2 = Real.exp (-x) := by
    dsimp [x, c]
    rw [heatFactor, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hid :
      x ^ m * Real.exp (-x) =
        c ^ m * (freqSq k ^ m * heatFactor ν t k ^ 2) := by
    rw [hheat]
    dsimp [x]
    rw [mul_pow]
    ring
  have hscaled :
      c ^ m * (freqSq k ^ m * heatFactor ν t k ^ 2)
        ≤ (Nat.factorial m : ℝ) := by
    rw [← hid]
    exact hmain
  have hcp : 0 < c ^ m := pow_pos hc m
  apply (le_div_iff₀ hcp).2
  simpa [c, mul_comm, mul_left_comm, mul_assoc] using hscaled

theorem smoothTerm_heat_le
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (a : Mode2 → ℂ) (k : Mode2) :
    smoothTerm m (heatCoeff ν t a) k
      ≤ ((Nat.factorial m : ℝ) / (2 * ν * t) ^ m) * l2Term a k := by
  unfold smoothTerm l2Term
  rw [norm_heatCoeff]
  calc
    freqSq k ^ m * (heatFactor ν t k * ‖a k‖) ^ 2
        = (freqSq k ^ m * heatFactor ν t k ^ 2) * ‖a k‖ ^ 2 := by
            ring
    _ ≤ ((Nat.factorial m : ℝ) / (2 * ν * t) ^ m) * ‖a k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (freqSq_pow_heatFactor_sq_le hν ht m k)
        (sq_nonneg _)

/-- Every L² shear is in every integer Sobolev class at every positive time. -/
theorem positive_time_smoothing
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (m : ℕ) (u : L2ShearDatum) :
    Summable (smoothTerm m (heatCoeff ν t u.coeff)) := by
  let C : ℝ := (Nat.factorial m : ℝ) / (2 * ν * t) ^ m
  exact Summable.of_nonneg_of_le
    (fun k => smoothTerm_nonneg m (heatCoeff ν t u.coeff) k)
    (fun k => by
      simpa [C] using smoothTerm_heat_le hν ht m u.coeff k)
    (u.l2Summable.mul_left C)

/-- Squared coefficient error relative to the initial profile. -/
def traceErrorTerm
    (ν t : ℝ) (a : Mode2 → ℂ) (k : Mode2) : ℝ :=
  ‖heatCoeff ν t a k - a k‖ ^ 2

theorem traceErrorTerm_nonneg
    (ν t : ℝ) (a : Mode2 → ℂ) (k : Mode2) :
    0 ≤ traceErrorTerm ν t a k := by
  exact sq_nonneg _

theorem traceErrorTerm_le_four
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Mode2 → ℂ) (k : Mode2) :
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
    (ν : ℝ) (a : Mode2 → ℂ) (k : Mode2) :
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
def traceErrorSq (ν t : ℝ) (a : Mode2 → ℂ) : ℝ :=
  ∑' k, traceErrorTerm ν t a k

/-- Strong L² convergence of the heat orbit to its input trace. -/
theorem traceErrorSq_tendsto_zero
    {ν : ℝ} (hν : 0 < ν) (u : L2ShearDatum) :
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

/-
Three-dimensional spectral geometry.
The physical wave number is `(0,k₀,k₁)` and the velocity is polarized
in coordinate zero.
-/

def physicalWaveNumber (k : Mode2) (i : Fin 3) : ℤ :=
  if i = 0 then 0 else if i = 1 then k 0 else k 1

def shearVelocityCoeff
    (ν t : ℝ) (u : L2ShearDatum)
    (k : Mode2) (i : Fin 3) : ℂ :=
  if i = 0 then heatCoeff ν t u.coeff k else 0

def derivativeSymbol (k : Mode2) (i : Fin 3) : ℂ :=
  ((2 * Real.pi * (physicalWaveNumber k i : ℝ) : ℝ) : ℂ) * Complex.I

def divergenceCoeff
    (ν t : ℝ) (u : L2ShearDatum) (k : Mode2) : ℂ :=
  ∑ i : Fin 3, derivativeSymbol k i * shearVelocityCoeff ν t u k i

@[simp] theorem divergenceCoeff_eq_zero
    (ν t : ℝ) (u : L2ShearDatum) (k : Mode2) :
    divergenceCoeff ν t u k = 0 := by
  simp [divergenceCoeff, derivativeSymbol, physicalWaveNumber,
    shearVelocityCoeff]

def advectiveScalar
    (ν t : ℝ) (u : L2ShearDatum)
    (p q : Mode2) : ℂ :=
  ∑ j : Fin 3,
    shearVelocityCoeff ν t u p j * derivativeSymbol q j

@[simp] theorem advectiveScalar_eq_zero
    (ν t : ℝ) (u : L2ShearDatum)
    (p q : Mode2) :
    advectiveScalar ν t u p q = 0 := by
  simp [advectiveScalar, derivativeSymbol, physicalWaveNumber,
    shearVelocityCoeff]

/-- Finite convolution coefficient of `(u·∇)u`. -/
def rawConvectionCoeff
    (S : Finset Mode2)
    (ν t : ℝ) (u : L2ShearDatum)
    (k : Mode2) (i : Fin 3) : ℂ :=
  ∑ p ∈ S,
    advectiveScalar ν t u p (k - p) *
      shearVelocityCoeff ν t u (k - p) i

@[simp] theorem rawConvectionCoeff_eq_zero
    (S : Finset Mode2)
    (ν t : ℝ) (u : L2ShearDatum)
    (k : Mode2) (i : Fin 3) :
    rawConvectionCoeff S ν t u k i = 0 := by
  simp [rawConvectionCoeff]

/-- Scalar coefficient ODE underlying the heat equation. -/
theorem heatFactor_hasDerivAt
    (ν t : ℝ) (k : Mode2) :
    HasDerivAt (fun s : ℝ => heatFactor ν s k)
      (-(ν * freqSq k) * heatFactor ν t k) t := by
  have hinner :
      HasDerivAt
        (fun s : ℝ => -(ν * s * freqSq k))
        (-(ν * freqSq k)) t :=
    ((hasDerivAt_const_mul (x := t) ν).mul_const (freqSq k)).neg
  simpa only [heatFactor, mul_comm] using hinner.exp

/--
Exact coefficient-level positive-time NSE certificate for the L² shear family.
No smallness premise and no H^(1/2) premise occur.
-/
structure PositiveTimeSpectralFlow
    (ν : ℝ) (u : L2ShearDatum) : Prop where
  initialCoefficient :
    ∀ k, heatCoeff ν 0 u.coeff k = u.coeff k
  strongL2Trace :
    Tendsto (fun t : ℝ => traceErrorSq ν t u.coeff)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
  allPositiveSobolevOrders :
    ∀ (t : ℝ), 0 < t →
      ∀ m : ℕ, Summable (smoothTerm m (heatCoeff ν t u.coeff))
  divergenceFree :
    ∀ (t : ℝ) (k : Mode2), divergenceCoeff ν t u k = 0
  convectionZero :
    ∀ (S : Finset Mode2) (t : ℝ) (k : Mode2) (i : Fin 3),
      rawConvectionCoeff S ν t u k i = 0
  heatODE :
    ∀ (t : ℝ) (k : Mode2),
      HasDerivAt (fun s : ℝ => heatFactor ν s k)
        (-(ν * freqSq k) * heatFactor ν t k) t

/--
Unconditional infinite-dimensional L² shear family, at the exact Fourier
coefficient level.
-/
theorem NSE_ROUGH_SHEAR_L2_FAMILY
    (ν : ℝ) (hν : 0 < ν) (u : L2ShearDatum) :
    PositiveTimeSpectralFlow ν u := by
  refine
    { initialCoefficient := ?_
      strongL2Trace := traceErrorSq_tendsto_zero hν u
      allPositiveSobolevOrders := ?_
      divergenceFree := ?_
      convectionZero := ?_
      heatODE := ?_ }
  · intro k
    exact heatCoeff_zero_time ν u.coeff k
  · intro t ht m
    exact positive_time_smoothing hν ht m u
  · intro t k
    exact divergenceCoeff_eq_zero ν t u k
  · intro S t k i
    exact rawConvectionCoeff_eq_zero S ν t u k i
  · intro t k
    exact heatFactor_hasDerivAt ν t k

/-- Critical H^(1/2) coefficient density. -/
def hhalfTerm (a : Mode2 → ℂ) (k : Mode2) : ℝ :=
  Real.sqrt (freqSq k) * ‖a k‖ ^ 2

def IsHhalf (u : L2ShearDatum) : Prop :=
  Summable (hhalfTerm u.coeff)

/-- The strict rough subfamily. -/
abbrev RoughL2ShearDatum :=
  {u : L2ShearDatum // ¬ IsHhalf u}

/--
Every strict `L² \ H^(1/2)` shear datum inherits the same unconditional
positive-time spectral regularity.
-/
theorem NSE_ROUGH_SHEAR_STRICT_SUBFAMILY
    (ν : ℝ) (hν : 0 < ν) (u : RoughL2ShearDatum) :
    PositiveTimeSpectralFlow ν u.1 :=
  NSE_ROUGH_SHEAR_L2_FAMILY ν hν u.1

/--
Logical union adapter.  The arbitrary smooth branch remains an explicit
premise; the rough-shear branch is unconditional.
-/
theorem regular_on_union
    {SmoothDatum : Type*}
    (SmoothRegular : SmoothDatum → Prop)
    (RoughRegular : L2ShearDatum → Prop)
    (hSmooth : ∀ a, SmoothRegular a)
    (hRough : ∀ a, RoughRegular a) :
    (∀ x : Sum SmoothDatum L2ShearDatum,
      Sum.elim SmoothRegular RoughRegular x) := by
  intro x
  cases x with
  | inl a => exact hSmooth a
  | inr a => exact hRough a

end NSERoughShearL2Family
