import H12_FOURIER_FOUNDATIONS
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace H12SpectralEnergyBridge

open H12FourierFoundations

/-- Total homogeneous critical `H^(1/2)` Fourier energy. -/
def hhalfSq (u : Mode3 → CVec3) : ℝ :=
  ∑' k : Mode3, hhalfTerm u k

/-- Homogeneous `H^1` Fourier energy density. -/
def honeTerm (u : Mode3 → CVec3) (k : Mode3) : ℝ :=
  (freq k) ^ 2 * ‖u k‖ ^ 2

theorem honeTerm_nonneg (u : Mode3 → CVec3) (k : Mode3) :
    0 ≤ honeTerm u k := by
  unfold honeTerm
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Finite critical `H^(1/2)` energy. -/
def hhalfFinset (S : Finset Mode3) (u : Mode3 → CVec3) : ℝ :=
  ∑ k ∈ S, hhalfTerm u k

/-- Finite `H^1` energy. -/
def honeFinset (S : Finset Mode3) (u : Mode3 → CVec3) : ℝ :=
  ∑ k ∈ S, honeTerm u k

/-- Finite `H^(3/2)` energy. -/
def hthreeHalfFinset (S : Finset Mode3) (u : Mode3 → CVec3) : ℝ :=
  ∑ k ∈ S, hthreeHalfTerm u k

theorem honeTerm_sq_eq_hhalf_mul_hthreeHalf
    (u : Mode3 → CVec3) (k : Mode3) :
    (honeTerm u k) ^ 2 =
      hhalfTerm u k * hthreeHalfTerm u k := by
  unfold honeTerm hhalfTerm hthreeHalfTerm
  ring

/--
Finite Fourier critical interpolation without fractional powers:
`H^1(S)^2 <= H^(1/2)(S) H^(3/2)(S)`.
-/
theorem finite_critical_interpolation
    (S : Finset Mode3) (u : Mode3 → CVec3) :
    (honeFinset S u) ^ 2 ≤
      hhalfFinset S u * hthreeHalfFinset S u := by
  unfold honeFinset hhalfFinset hthreeHalfFinset
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := S)
    (r := fun k => honeTerm u k)
    (f := fun k => hhalfTerm u k)
    (g := fun k => hthreeHalfTerm u k)
  · intro k hk
    exact hhalfTerm_nonneg u k
  · intro k hk
    exact hthreeHalfTerm_nonneg u k
  · intro k hk
    exact (honeTerm_sq_eq_hhalf_mul_hthreeHalf u k).le

/-- Total critical energy is nonnegative for a summable critical datum. -/
theorem hhalfSq_nonneg (u : H12Datum) :
    0 ≤ hhalfSq u.coeff := by
  unfold hhalfSq
  exact tsum_nonneg (fun k => hhalfTerm_nonneg u.coeff k)

/--
The already-proved pointwise heat contraction lifts to the full critical
Fourier energy by summable monotonicity.
-/
theorem heat_hhalfSq_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : H12Datum) :
    hhalfSq (heatDatum ν t hν ht u).coeff ≤
      hhalfSq u.coeff := by
  unfold hhalfSq
  exact (heatDatum ν t hν ht u).hhalfSummable.tsum_le_tsum
    (fun k => hhalfTerm_heat_le hν ht u.coeff k)
    u.hhalfSummable

/--
The Fourier character product law in exactly the three-torus mode type used
by the critical coefficient model.
-/
theorem torus_character_product
    (k l : Mode3) (x : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier (k + l) x =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x := by
  exact UnitAddTorus.mFourier_add

/--
Audited spectral-energy bridge.  It contains no fractional Sobolev embedding
and no NSE local-existence or continuation premise.
-/
structure SpectralEnergyBundle : Prop where
  heatCriticalContraction :
    ∀ (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) (u : H12Datum),
      hhalfSq (heatDatum ν t hν ht u).coeff ≤ hhalfSq u.coeff
  finiteInterpolation :
    ∀ (S : Finset Mode3) (u : Mode3 → CVec3),
      (honeFinset S u) ^ 2 ≤
        hhalfFinset S u * hthreeHalfFinset S u

theorem H12_SPECTRAL_ENERGY_BRIDGE : SpectralEnergyBundle := by
  refine ⟨?_, finite_critical_interpolation⟩
  intro ν t hν ht u
  exact heat_hhalfSq_le hν ht u

end H12SpectralEnergyBridge
