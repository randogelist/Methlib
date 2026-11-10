import NSE_ROUGH_SHEAR_L2_FAMILY
import Mathlib.Analysis.PSeries

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace NSERoughShearL2Family
namespace StrictNonemptyWitness

/--
The scalar Fourier coefficient of the explicit rough shear datum.

It is supported on the first frequency axis and equals `1 / |n|` there.
At the zero mode the field convention `1 / 0 = 0` gives the required
mean-zero coefficient.
-/
def harmonicCoeff (k : Mode2) : ℂ :=
  if k 1 = 0 then
    ((1 / |(k 0 : ℝ)| : ℝ) : ℂ)
  else
    0

@[simp] theorem harmonicCoeff_zero :
    harmonicCoeff (0 : Mode2) = 0 := by
  simp [harmonicCoeff]

theorem harmonicCoeff_reality (k : Mode2) :
    harmonicCoeff (-k) = star (harmonicCoeff k) := by
  by_cases hk : k 1 = 0 <;>
    simp [harmonicCoeff, hk, Complex.star_def]

/--
On product coordinates, the squared coefficient is the integer `p = 2`
summand on the axis and vanishes off the axis.
-/
theorem harmonic_l2Term_pair (z w : ℤ) :
    l2Term harmonicCoeff ![z, w] =
      if w = 0 then 1 / (z : ℝ) ^ 2 else 0 := by
  by_cases hw : w = 0
  · subst w
    simp [harmonicCoeff, l2Term, sq_abs]
  · simp [harmonicCoeff, l2Term, hw]

theorem harmonic_l2_hasSum (z : ℤ) :
    HasSum
      (fun w : ℤ => l2Term harmonicCoeff ![z, w])
      (1 / (z : ℝ) ^ 2) := by
  convert hasSum_ite_eq (0 : ℤ) (1 / (z : ℝ) ^ 2) using 1
  funext w
  exact harmonic_l2Term_pair z w

/--
The explicit coefficient family is square-summable. The proof transports
the two-dimensional mode sum to `ℤ × ℤ`, sums the single supported point in
the second coordinate, and applies the integer `p = 2` series theorem.
-/
theorem harmonicCoeff_l2Summable :
    Summable (l2Term harmonicCoeff) := by
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff]
  simp only [Function.comp_def, finTwoArrowEquiv_symm_apply]
  refine
    (summable_prod_of_nonneg
      (fun p : ℤ × ℤ =>
        l2Term_nonneg harmonicCoeff ![p.1, p.2])).2 ?_
  constructor
  · intro z
    exact (harmonic_l2_hasSum z).summable
  · have hp :
        Summable (fun z : ℤ => 1 / (z : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    exact hp.congr fun z => (harmonic_l2_hasSum z).tsum_eq.symm

/-- The explicit real, mean-zero `L²` shear datum. -/
def harmonicDatum : L2ShearDatum where
  coeff := harmonicCoeff
  meanZero := harmonicCoeff_zero
  reality := harmonicCoeff_reality
  l2Summable := harmonicCoeff_l2Summable

/-- Positive first-axis modes used to expose the harmonic divergence. -/
def axisMode (n : ℕ) : Mode2 :=
  ![((n + 1 : ℕ) : ℤ), 0]

theorem axisMode_injective :
    Function.Injective axisMode := by
  intro m n h
  have h0 := congrFun h (0 : Fin 2)
  simp [axisMode] at h0
  omega

@[simp] theorem harmonicCoeff_axisMode (n : ℕ) :
    harmonicCoeff (axisMode n) =
      ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  simp [harmonicCoeff, axisMode, abs_of_nonneg hn]

theorem harmonicCoeff_axis_norm_sq (n : ℕ) :
    ‖harmonicCoeff (axisMode n)‖ ^ 2 =
      1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  rw [harmonicCoeff_axisMode, Complex.norm_real]
  have hnonneg :
      0 ≤ (1 / ((n + 1 : ℕ) : ℝ)) := by
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  field_simp [hne]

theorem freqSq_axisMode (n : ℕ) :
    freqSq (axisMode n) =
      ((2 * Real.pi) * ((n + 1 : ℕ) : ℝ)) ^ 2 := by
  simp [freqSq, axisMode]
  ring

/--
Along the positive axis the critical `H^(1/2)` density is exactly a
nonzero constant times the shifted harmonic series.
-/
theorem hhalfTerm_axisMode (n : ℕ) :
    hhalfTerm harmonicCoeff (axisMode n) =
      (2 * Real.pi) * (1 / ((n + 1 : ℕ) : ℝ)) := by
  unfold hhalfTerm
  rw [freqSq_axisMode, Real.sqrt_sq_eq_abs,
    harmonicCoeff_axis_norm_sq]
  have hp :
      0 ≤ (2 * Real.pi) * ((n + 1 : ℕ) : ℝ) := by
    positivity
  rw [abs_of_nonneg hp]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  field_simp [hn]

theorem not_summable_shifted_harmonic :
    ¬ Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
  intro hs
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).1
  simpa only [Nat.cast_add, Nat.cast_one] using hs

theorem not_summable_hhalf_axis :
    ¬ Summable
      (fun n : ℕ => hhalfTerm harmonicCoeff (axisMode n)) := by
  intro hs
  have hscaled :=
    hs.mul_left ((2 * Real.pi)⁻¹)
  have hharm :
      Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    refine hscaled.congr ?_
    intro n
    rw [hhalfTerm_axisMode]
    simp [mul_assoc]
  exact not_summable_shifted_harmonic hharm

/-- The explicit datum fails the critical `H^(1/2)` summability condition. -/
theorem harmonicDatum_not_hhalf :
    ¬ IsHhalf harmonicDatum := by
  intro h
  have hall :
      Summable (hhalfTerm harmonicCoeff) := by
    simpa [IsHhalf, harmonicDatum] using h
  have haxis :
      Summable
        (fun n : ℕ => hhalfTerm harmonicCoeff (axisMode n)) := by
    simpa [Function.comp_def] using
      hall.comp_injective axisMode_injective
  exact not_summable_hhalf_axis haxis

/-- A concrete inhabitant of the strict rough shear subtype. -/
def explicitRoughDatum : RoughL2ShearDatum :=
  ⟨harmonicDatum, harmonicDatum_not_hhalf⟩

/-- Exact nonemptiness theorem requested for the strict `L² \ H^(1/2)` class. -/
theorem NSE_ROUGH_SHEAR_STRICT_SUBFAMILY_NONEMPTY :
    Nonempty RoughL2ShearDatum :=
  ⟨explicitRoughDatum⟩

/--
The nonemptiness witness composed with the previously A-tiered unconditional
family theorem.
-/
theorem EXISTS_NSE_ROUGH_SHEAR_STRICT_POSITIVE_TIME_FLOW
    (ν : ℝ) (hν : 0 < ν) :
    ∃ u : RoughL2ShearDatum,
      PositiveTimeSpectralFlow ν u.1 :=
  ⟨explicitRoughDatum,
    NSE_ROUGH_SHEAR_STRICT_SUBFAMILY ν hν explicitRoughDatum⟩

end StrictNonemptyWitness
end NSERoughShearL2Family
