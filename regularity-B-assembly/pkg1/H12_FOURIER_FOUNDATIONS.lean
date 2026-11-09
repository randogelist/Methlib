import Mathlib
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace H12FourierFoundations

/-- Integer frequency labels on the unit three-torus. -/
abbrev Mode3 := Fin 3 → ℤ

/-- Real and complex three-component Euclidean vectors. -/
abbrev RVec3 := EuclideanSpace ℝ (Fin 3)
abbrev CVec3 := EuclideanSpace ℂ (Fin 3)

/-- The real frequency vector associated to an integer Fourier mode. -/
def modeReal (k : Mode3) : RVec3 :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- The complexified frequency vector. -/
def modeComplex (k : Mode3) : CVec3 :=
  WithLp.toLp 2 (fun i => (k i : ℂ))

theorem modeReal_zero :
    modeReal (0 : Mode3) = 0 := by
  ext i
  simp [modeReal]

theorem modeReal_add (k l : Mode3) :
    modeReal (k + l) = modeReal k + modeReal l := by
  ext i
  simp [modeReal]

theorem modeReal_neg (k : Mode3) :
    modeReal (-k) = -modeReal k := by
  ext i
  simp [modeReal]

/-- Physical frequency magnitude `2π |k|`. -/
def freq (k : Mode3) : ℝ :=
  2 * Real.pi * ‖modeReal k‖

theorem freq_nonneg (k : Mode3) :
    0 ≤ freq k := by
  unfold freq
  positivity

theorem freq_zero :
    freq (0 : Mode3) = 0 := by
  simp [freq, modeReal_zero]

theorem freq_neg (k : Mode3) :
    freq (-k) = freq k := by
  rw [freq, modeReal_neg, norm_neg]
  rfl

theorem freq_add_le (k l : Mode3) :
    freq (k + l) ≤ freq k + freq l := by
  rw [freq, modeReal_add, freq, freq]
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    2 * Real.pi * ‖modeReal k + modeReal l‖
        ≤ 2 * Real.pi * (‖modeReal k‖ + ‖modeReal l‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hπ
    _ = 2 * Real.pi * ‖modeReal k‖ +
        2 * Real.pi * ‖modeReal l‖ := by ring

/--
The solenoidal Fourier fiber at frequency `k`.  The common physical factor
`2π i` is omitted because it does not affect the zero-divergence condition.
-/
def solenoidalSubmodule (k : Mode3) : Submodule ℂ CVec3 :=
  (innerSL ℂ (modeComplex k)).ker

def SolenoidalAt (k : Mode3) (v : CVec3) : Prop :=
  v ∈ solenoidalSubmodule k

/-- Modewise orthogonal Leray projection. -/
noncomputable def leray (k : Mode3) : CVec3 →L[ℂ] CVec3 :=
  (solenoidalSubmodule k).subtypeL.comp
    (solenoidalSubmodule k).orthogonalProjectionOnto

theorem leray_solenoidal (k : Mode3) (v : CVec3) :
    SolenoidalAt k (leray k v) := by
  change
    ((solenoidalSubmodule k).orthogonalProjectionOnto v : CVec3)
      ∈ solenoidalSubmodule k
  exact ((solenoidalSubmodule k).orthogonalProjectionOnto v).property

theorem leray_norm_le (k : Mode3) (v : CVec3) :
    ‖leray k v‖ ≤ ‖v‖ := by
  simpa [leray] using
    (solenoidalSubmodule k).norm_orthogonalProjectionOnto_apply_le v

/-- Critical homogeneous `H^(1/2)` coefficient density. -/
def hhalfTerm (u : Mode3 → CVec3) (k : Mode3) : ℝ :=
  freq k * ‖u k‖ ^ 2

/-- Critical homogeneous `H^(3/2)` coefficient density. -/
def hthreeHalfTerm (u : Mode3 → CVec3) (k : Mode3) : ℝ :=
  (freq k) ^ 3 * ‖u k‖ ^ 2

theorem hhalfTerm_nonneg (u : Mode3 → CVec3) (k : Mode3) :
    0 ≤ hhalfTerm u k := by
  unfold hhalfTerm
  exact mul_nonneg (freq_nonneg k) (sq_nonneg _)

theorem hthreeHalfTerm_nonneg (u : Mode3 → CVec3) (k : Mode3) :
    0 ≤ hthreeHalfTerm u k := by
  unfold hthreeHalfTerm
  exact mul_nonneg (pow_nonneg (freq_nonneg k) 3) (sq_nonneg _)

/--
A complexified mean-zero divergence-free critical Fourier datum.
The real-valued conjugation symmetry can be added as a later subspace;
it is not needed for the weighted Hilbert estimates.
-/
structure H12Datum where
  coeff : Mode3 → CVec3
  meanZero : coeff 0 = 0
  solenoidal : ∀ k, SolenoidalAt k (coeff k)
  hhalfSummable : Summable (hhalfTerm coeff)

/-- Heat multiplier on one mode. -/
def heatFactor (ν t : ℝ) (k : Mode3) : ℝ :=
  Real.exp (-ν * (freq k) ^ 2 * t)

theorem heatFactor_pos (ν t : ℝ) (k : Mode3) :
    0 < heatFactor ν t k := by
  unfold heatFactor
  positivity

theorem heatFactor_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : Mode3) :
    heatFactor ν t k ≤ 1 := by
  unfold heatFactor
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ ν * (freq k) ^ 2 * t := by
    exact mul_nonneg (mul_nonneg hν (sq_nonneg _)) ht
  linarith

/-- Heat evolution of a Fourier coefficient. -/
def heatCoeff (ν t : ℝ) (u : Mode3 → CVec3) (k : Mode3) : CVec3 :=
  ((heatFactor ν t k : ℝ) : ℂ) • u k

theorem heatCoeff_zero_time (ν : ℝ) (u : Mode3 → CVec3) (k : Mode3) :
    heatCoeff ν 0 u k = u k := by
  simp [heatCoeff, heatFactor]

theorem heatCoeff_solenoidal
    (ν t : ℝ) (u : Mode3 → CVec3) (k : Mode3)
    (hu : SolenoidalAt k (u k)) :
    SolenoidalAt k (heatCoeff ν t u k) := by
  change
    ((heatFactor ν t k : ℝ) : ℂ) • u k ∈ solenoidalSubmodule k
  exact (solenoidalSubmodule k).smul_mem _ hu

theorem hhalfTerm_heat_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : Mode3 → CVec3) (k : Mode3) :
    hhalfTerm (fun j => heatCoeff ν t u j) k ≤ hhalfTerm u k := by
  have hpos : 0 ≤ heatFactor ν t k := (heatFactor_pos ν t k).le
  have hle : heatFactor ν t k ≤ 1 := heatFactor_le_one hν ht k
  have hnorm :
      ‖heatCoeff ν t u k‖ = heatFactor ν t k * ‖u k‖ := by
    simp [heatCoeff, norm_smul, abs_of_nonneg hpos]
  rw [hhalfTerm, hhalfTerm, hnorm]
  have hf : 0 ≤ freq k := freq_nonneg k
  have hsq : (heatFactor ν t k) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (heatFactor ν t k)]
  calc
    freq k * (heatFactor ν t k * ‖u k‖) ^ 2
        = (freq k * (heatFactor ν t k) ^ 2) * ‖u k‖ ^ 2 := by
            ring
    _ ≤ (freq k * 1) * ‖u k‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq hf) (sq_nonneg _)
    _ = freq k * ‖u k‖ ^ 2 := by ring

/-- Heat evolution preserves the critical datum class for nonnegative time. -/
noncomputable def heatDatum
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : H12Datum) : H12Datum where
  coeff := fun k => heatCoeff ν t u.coeff k
  meanZero := by
    simp [heatCoeff, u.meanZero]
  solenoidal := by
    intro k
    exact heatCoeff_solenoidal ν t u.coeff k (u.solenoidal k)
  hhalfSummable := by
    exact Summable.of_nonneg_of_le
      (fun k => hhalfTerm_nonneg (fun j => heatCoeff ν t u.coeff j) k)
      (fun k => hhalfTerm_heat_le hν ht u.coeff k)
      u.hhalfSummable

theorem heatDatum_coeff
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : H12Datum) (k : Mode3) :
    (heatDatum ν t hν ht u).coeff k = heatCoeff ν t u.coeff k := by
  rfl

/-- Fourier derivative symbol for coordinate `j`. -/
def derivSymbol (q : Mode3) (j : Fin 3) : ℂ :=
  ((2 * Real.pi * (q j : ℝ) : ℝ) : ℂ) * Complex.I

/-- Scalar contraction `u_p · (i 2π q)`. -/
def advectiveScalar
    (u : Mode3 → CVec3) (p q : Mode3) : ℂ :=
  ∑ j : Fin 3, u p j * derivSymbol q j

/--
Finite-support raw Fourier coefficient of `(u · ∇)v`.
Only the left input support is enumerated here; this is sufficient as a
finite algebraic core and is independent of convergence issues.
-/
def rawTransportCoeff
    (S : Finset Mode3)
    (u v : Mode3 → CVec3)
    (k : Mode3) : CVec3 :=
  WithLp.toLp 2 (fun i =>
    ∑ p ∈ S,
      advectiveScalar u p (k - p) * v (k - p) i)

theorem rawTransport_zero_left
    (S : Finset Mode3) (v : Mode3 → CVec3) (k : Mode3) :
    rawTransportCoeff S 0 v k = 0 := by
  ext i
  simp [rawTransportCoeff, advectiveScalar]

theorem rawTransport_zero_right
    (S : Finset Mode3) (u : Mode3 → CVec3) (k : Mode3) :
    rawTransportCoeff S u 0 k = 0 := by
  ext i
  simp [rawTransportCoeff]

/-- Finite projected NSE transport coefficient. -/
noncomputable def projectedTransportCoeff
    (S : Finset Mode3)
    (u v : Mode3 → CVec3)
    (k : Mode3) : CVec3 :=
  leray k (rawTransportCoeff S u v k)

theorem projectedTransport_solenoidal
    (S : Finset Mode3)
    (u v : Mode3 → CVec3)
    (k : Mode3) :
    SolenoidalAt k (projectedTransportCoeff S u v k) := by
  exact leray_solenoidal k (rawTransportCoeff S u v k)

theorem projectedTransport_norm_le
    (S : Finset Mode3)
    (u v : Mode3 → CVec3)
    (k : Mode3) :
    ‖projectedTransportCoeff S u v k‖
      ≤ ‖rawTransportCoeff S u v k‖ := by
  exact leray_norm_le k (rawTransportCoeff S u v k)

/-- Direct wrapper around the multiplicative character law. -/
theorem torus_fourier_add
    (k l : Mode3) (x : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier (k + l) x =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x := by
  exact UnitAddTorus.mFourier_add

/--
Audited root bundle for the unconditional spectral/algebraic foundation.
No fractional Sobolev embedding, local NSE existence, or continuation
principle appears as a premise or conclusion.
-/
structure FoundationBundle : Prop where
  frequencyNonnegative : ∀ k : Mode3, 0 ≤ freq k
  frequencySubadditive :
    ∀ k l : Mode3, freq (k + l) ≤ freq k + freq l
  projectionSolenoidal :
    ∀ k : Mode3, ∀ v : CVec3, SolenoidalAt k (leray k v)
  projectionContractive :
    ∀ k : Mode3, ∀ v : CVec3, ‖leray k v‖ ≤ ‖v‖
  heatPreservesSolenoidal :
    ∀ ν t : ℝ, ∀ u : Mode3 → CVec3, ∀ k : Mode3,
      SolenoidalAt k (u k) →
      SolenoidalAt k (heatCoeff ν t u k)
  projectedTransportSolenoidal :
    ∀ S : Finset Mode3, ∀ u v : Mode3 → CVec3, ∀ k : Mode3,
      SolenoidalAt k (projectedTransportCoeff S u v k)

theorem H12_FOURIER_FOUNDATIONS : FoundationBundle := by
  refine
    ⟨freq_nonneg,
      freq_add_le,
      leray_solenoidal,
      leray_norm_le,
      ?_,
      projectedTransport_solenoidal⟩
  intro ν t u k hu
  exact heatCoeff_solenoidal ν t u k hu

end H12FourierFoundations
