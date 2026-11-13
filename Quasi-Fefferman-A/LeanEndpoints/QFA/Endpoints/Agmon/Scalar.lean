import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# QFA: scalar Agmon and nonlinear absorption endpoints

Prepared source candidates only. No Lean execution or theorem-level axiom audit has
been performed. These are scalar implications; they do not establish a physical
Sobolev estimate, an NSE solution, or the QFA root theorem.

Source pin: Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, Lean 4.33.0.
Mathematical locations: QFA B-tier D06.06--D06.08 and D07.
EP071 supplies integral Cauchy--Schwarz upstream; the present file starts after
those physical estimates have been supplied as explicit real inequalities.

Additional inspected scalar sources, with stable B-tier index identifiers:
* EP111 Real.pi_pos: Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:157.
* EP112 Real.sqrt_nonneg: Mathlib/Analysis/Real/Sqrt.lean:144.
* EP113 Real.sq_sqrt: Mathlib/Analysis/Real/Sqrt.lean:178.
* EP114 pow_le_pow_left₀: Mathlib/Algebra/Order/GroupWithZero/Basic.lean:470.
* EP115 le_of_pow_le_pow_left₀: same file:702.
* EP116 lt_of_pow_lt_pow_left₀: same file:699.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QFA.Endpoints.Agmon

noncomputable section

/-- Scalar data expected from the physical endpoint.

`E`, `D`, and `Z` denote squared L2 velocity, Frobenius-gradient, and Laplacian
norms. `A` is the nonnegative L-infinity norm and `N` a nonnegative nonlinear
pairing bound. Every analytic inequality is an explicit premise.
-/
structure ScalarProfile (E D Z A N : ℝ) : Prop where
  energy_nonneg : 0 ≤ E
  gradient_nonneg : 0 ≤ D
  laplacian_nonneg : 0 ≤ Z
  amplitude_nonneg : 0 ≤ A
  nonlinear_nonneg : 0 ≤ N
  interpolation : D ^ 2 ≤ E * Z
  agmon : A ^ 2 ≤ Real.sqrt (D * Z) / (2 * Real.pi)
  convection : N ≤ A * Real.sqrt D * Real.sqrt Z

private theorem four_pi_sq_pos : 0 < 4 * Real.pi ^ 2 := by
  -- EP111: denominator and cancellation constant positivity.
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

private theorem sqrt_fourth (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x ^ 4 = x ^ 2 := by
  calc
    Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 := by ring
    -- EP113: the nonnegative radicand identifies its squared square root.
    _ = x ^ 2 := by rw [Real.sq_sqrt hx]

/-- D06.06, with the positive constant cleared before taking a square. -/
theorem agmon_fourth_power
    {D Z A : ℝ} (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hAgmon : A ^ 2 ≤ Real.sqrt (D * Z) / (2 * Real.pi)) :
    4 * Real.pi ^ 2 * A ^ 4 ≤ D * Z := by
  -- EP111: the Agmon denominator is strictly positive.
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscaled : (2 * Real.pi) * A ^ 2 ≤ Real.sqrt (D * Z) := by
    simpa only [mul_comm] using (le_div_iff₀ hpi).mp hAgmon
  calc
    4 * Real.pi ^ 2 * A ^ 4 = ((2 * Real.pi) * A ^ 2) ^ 2 := by ring
    -- EP114: square the nonnegative left side after clearing the denominator.
    _ ≤ Real.sqrt (D * Z) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hpi.le (sq_nonneg A)) hscaled 2
    -- EP113: D*Z is nonnegative.
    _ = D * Z := Real.sq_sqrt (mul_nonneg hD hZ)

/-- D06.08 in an exact polynomial form, with no fractional real powers.

This statement includes `D = 0` and `Z = 0`; no division by either quantity occurs.
-/
theorem nonlinear_fourth_power_of_agmon_fourth
    {E D Z A N : ℝ} (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hN : 0 ≤ N)
    (hInterpolation : D ^ 2 ≤ E * Z)
    (hAgmon : 4 * Real.pi ^ 2 * A ^ 4 ≤ D * Z)
    (hConvection : N ≤ A * Real.sqrt D * Real.sqrt Z) :
    4 * Real.pi ^ 2 * N ^ 4 ≤ (E * D) * Z ^ 4 := by
  have hNfourth : N ^ 4 ≤ A ^ 4 * D ^ 2 * Z ^ 2 := by
    calc
      -- EP114: N is nonnegative; hConvection bounds its fourth power.
      N ^ 4 ≤ (A * Real.sqrt D * Real.sqrt Z) ^ 4 :=
        pow_le_pow_left₀ hN hConvection 4
      _ = A ^ 4 * D ^ 2 * Z ^ 2 := by
        rw [mul_pow, mul_pow, sqrt_fourth D hD, sqrt_fourth Z hZ]
  calc
    4 * Real.pi ^ 2 * N ^ 4 ≤
        (4 * Real.pi ^ 2) * (A ^ 4 * D ^ 2 * Z ^ 2) :=
      mul_le_mul_of_nonneg_left hNfourth four_pi_sq_pos.le
    _ = (4 * Real.pi ^ 2 * A ^ 4) * (D ^ 2 * Z ^ 2) := by ring
    _ ≤ (D * Z) * (D ^ 2 * Z ^ 2) :=
      mul_le_mul_of_nonneg_right hAgmon (mul_nonneg (sq_nonneg D) (sq_nonneg Z))
    _ = D ^ 2 * (D * Z ^ 3) := by ring
    _ ≤ (E * Z) * (D * Z ^ 3) :=
      mul_le_mul_of_nonneg_right hInterpolation (mul_nonneg hD (pow_nonneg hZ 3))
    _ = (E * D) * Z ^ 4 := by ring

/-- The scalar profile yields the exact fourth-power nonlinear estimate. -/
theorem ScalarProfile.nonlinear_fourth_power
    {E D Z A N : ℝ} (h : ScalarProfile E D Z A N) :
    4 * Real.pi ^ 2 * N ^ 4 ≤ (E * D) * Z ^ 4 :=
  nonlinear_fourth_power_of_agmon_fourth h.gradient_nonneg h.laplacian_nonneg
    h.nonlinear_nonneg h.interpolation
    (agmon_fourth_power h.gradient_nonneg h.laplacian_nonneg h.agmon) h.convection

/-- Any nonnegative coefficient whose fourth power bounds the energy product
absorbs the nonlinear term. This statement also covers `Z = 0`.
-/
theorem nonlinear_le_of_product_le
    {E D Z N c : ℝ} (hZ : 0 ≤ Z) (hc : 0 ≤ c)
    (hFourth : 4 * Real.pi ^ 2 * N ^ 4 ≤ (E * D) * Z ^ 4)
    (hProduct : E * D ≤ 4 * Real.pi ^ 2 * c ^ 4) :
    N ≤ c * Z := by
  have hscaled : 4 * Real.pi ^ 2 * N ^ 4 ≤
      (4 * Real.pi ^ 2) * (c * Z) ^ 4 := by
    calc
      4 * Real.pi ^ 2 * N ^ 4 ≤ (E * D) * Z ^ 4 := hFourth
      _ ≤ (4 * Real.pi ^ 2 * c ^ 4) * Z ^ 4 :=
        mul_le_mul_of_nonneg_right hProduct (pow_nonneg hZ 4)
      _ = (4 * Real.pi ^ 2) * (c * Z) ^ 4 := by ring
  have hpow : N ^ 4 ≤ (c * Z) ^ 4 :=
    le_of_mul_le_mul_left hscaled four_pi_sq_pos
  -- EP115: only the target c*Z must be nonnegative for order reflection.
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (mul_nonneg hc hZ) hpow

/-- An exact nested-square-root representative of
`(2*pi)^(-1/2) * (E*D)^(1/4)` on nonnegative energies.

The present file uses its fourth-power identity, avoiding an additional rpow
normalization adapter.
-/
def nonlinearCoefficient (E D : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt ((E * D) / (4 * Real.pi ^ 2)))

theorem nonlinearCoefficient_nonneg (E D : ℝ) :
    0 ≤ nonlinearCoefficient E D :=
  -- EP112: the outer square root is nonnegative for every real radicand.
  Real.sqrt_nonneg _

/-- Exact coefficient identity; denominator positivity is independent of E,D. -/
theorem nonlinearCoefficient_fourth
    {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) :
    4 * Real.pi ^ 2 * nonlinearCoefficient E D ^ 4 = E * D := by
  have hq : 0 ≤ (E * D) / (4 * Real.pi ^ 2) :=
    div_nonneg (mul_nonneg hE hD) four_pi_sq_pos.le
  have hfourth : nonlinearCoefficient E D ^ 4 = (E * D) / (4 * Real.pi ^ 2) := by
    unfold nonlinearCoefficient
    -- EP112 and EP113: the two nested square roots have the prescribed fourth power.
    rw [sqrt_fourth _ (Real.sqrt_nonneg _), Real.sq_sqrt hq]
  rw [hfourth]
  calc
    4 * Real.pi ^ 2 * ((E * D) / (4 * Real.pi ^ 2)) =
        ((E * D) / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2) := mul_comm _ _
    _ = E * D := div_mul_cancel₀ _ four_pi_sq_pos.ne'

/-- The frozen product threshold produces a strictly positive viscosity margin. -/
theorem nonlinearCoefficient_lt_viscosity
    {E D ν : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) (hν : 0 < ν)
    (hSmall : E * D < 4 * Real.pi ^ 2 * ν ^ 4) :
    nonlinearCoefficient E D < ν := by
  have hscaled : (4 * Real.pi ^ 2) * nonlinearCoefficient E D ^ 4 <
      (4 * Real.pi ^ 2) * ν ^ 4 := by
    rw [nonlinearCoefficient_fourth hE hD]
    exact hSmall
  have hpow : nonlinearCoefficient E D ^ 4 < ν ^ 4 :=
    lt_of_mul_lt_mul_left hscaled four_pi_sq_pos.le
  -- EP116: strict fourth-power comparison reflects through nonnegative viscosity.
  exact lt_of_pow_lt_pow_left₀ 4 hν.le hpow

/-- Quantitative nonlinear estimate, including all zero-energy cases. -/
theorem ScalarProfile.nonlinear_le_coefficient
    {E D Z A N : ℝ} (h : ScalarProfile E D Z A N) :
    N ≤ nonlinearCoefficient E D * Z := by
  apply nonlinear_le_of_product_le h.laplacian_nonneg (nonlinearCoefficient_nonneg E D)
    h.nonlinear_fourth_power
  exact le_of_eq (nonlinearCoefficient_fourth h.energy_nonneg h.gradient_nonneg).symm

/-- Explicit zero-dissipation case; no cancellation by Z is used. -/
theorem ScalarProfile.nonlinear_eq_zero_of_laplacian_eq_zero
    {E D Z A N : ℝ} (h : ScalarProfile E D Z A N) (hZ : Z = 0) : N = 0 := by
  apply le_antisymm
  · simpa only [hZ, mul_zero] using h.nonlinear_le_coefficient
  · exact h.nonlinear_nonneg

/-- A purely scalar absorption step for an already supplied enstrophy inequality.

The real number `d` denotes its derivative value; this theorem asserts no
derivative existence or Navier--Stokes identity.
-/
theorem ScalarProfile.enstrophy_absorption
    {E D Z A N d ν : ℝ} (h : ScalarProfile E D Z A N)
    (hEnstrophy : d / 2 + ν * Z ≤ N) :
    d + 2 * (ν - nonlinearCoefficient E D) * Z ≤ 0 := by
  have hNonlinear := h.nonlinear_le_coefficient
  nlinarith only [hEnstrophy, hNonlinear]

/-- Positive uniform dissipation margin under the strict product threshold. -/
theorem ScalarProfile.viscosity_margin_pos
    {E D Z A N ν : ℝ} (h : ScalarProfile E D Z A N) (hν : 0 < ν)
    (hSmall : E * D < 4 * Real.pi ^ 2 * ν ^ 4) :
    0 < ν - nonlinearCoefficient E D :=
  sub_pos.mpr (nonlinearCoefficient_lt_viscosity h.energy_nonneg h.gradient_nonneg hν hSmall)

end

end QFA.Endpoints.Agmon
