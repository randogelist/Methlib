import H12_SPECTRAL_ENERGY_BRIDGE

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace H12SigmaZeroSmallClass

open H12FourierFoundations H12SpectralEnergyBridge

/--
Real-valuedness at the Fourier-coefficient level.  This is the conjugation
symmetry of an actual real field, rather than a componentwise reality
requirement on each (generally complex) Fourier coefficient.
-/
def ConjugateReality (a : Mode3 → CVec3) : Prop :=
  ∀ (k : Mode3) (i : Fin 3), a (-k) i = star (a k i)

/--
A real, mean-zero, solenoidal critical Fourier datum.  Physical Fourier
synthesis and identification with a function-space norm are separate
endpoints; this structure does not assert either an NSE evolution or its
regularity.
-/
structure RealH12Datum extends H12Datum where
  reality : ConjugateReality coeff

/-- The squared critical coefficient norm, with physical weight `2π |k|`. -/
def criticalSq (a : RealH12Datum) : ℝ :=
  hhalfSq a.coeff

/-- The associated nonnegative critical coefficient norm. -/
def criticalNorm (a : RealH12Datum) : ℝ :=
  Real.sqrt (criticalSq a)

theorem criticalSq_nonneg (a : RealH12Datum) :
    0 ≤ criticalSq a := by
  exact hhalfSq_nonneg a.toH12Datum

theorem criticalNorm_nonneg (a : RealH12Datum) :
    0 ≤ criticalNorm a := by
  exact Real.sqrt_nonneg _

theorem criticalNorm_sq (a : RealH12Datum) :
    criticalNorm a ^ 2 = criticalSq a := by
  exact Real.sq_sqrt (criticalSq_nonneg a)

/--
The conservative radius used by the existing critical-energy assembly.
`C3` is a numerical parameter here.  The existence of a physical Sobolev
certificate with this constant is not included in the carrier definition.
-/
def smallRadius (ν C3 : ℝ) : ℝ :=
  ν / (8 * C3 ^ 3)

theorem smallRadius_pos {ν C3 : ℝ}
    (hν : 0 < ν) (hC3 : 0 < C3) :
    0 < smallRadius ν C3 := by
  unfold smallRadius
  positivity

/-- Quantitative smallness in the concrete real critical coefficient class. -/
def Small (ν C3 : ℝ) (a : RealH12Datum) : Prop :=
  0 < ν ∧ 0 < C3 ∧ criticalSq a < smallRadius ν C3 ^ 2

/-- The small real, solenoidal, mean-zero critical coefficient carrier. -/
abbrev SmallDatum (ν C3 : ℝ) :=
  {a : RealH12Datum // Small ν C3 a}

theorem small_norm_lt {ν C3 : ℝ} {a : RealH12Datum}
    (ha : Small ν C3 a) :
    criticalNorm a < smallRadius ν C3 := by
  have hr := smallRadius_pos ha.1 ha.2.1
  have hn := criticalNorm_nonneg a
  have hs := criticalNorm_sq a
  have hsmall := ha.2.2
  nlinarith

/-- The zero datum witnesses nonvacuity without any analytic admission. -/
def zeroDatum : RealH12Datum where
  coeff := 0
  meanZero := rfl
  solenoidal := by
    intro k
    exact (solenoidalSubmodule k).zero_mem
  hhalfSummable := by
    change Summable (fun k : Mode3 => hhalfTerm (0 : Mode3 → CVec3) k)
    simpa [hhalfTerm] using
      (summable_zero : Summable (fun _ : Mode3 => (0 : ℝ)))
  reality := by
    intro k i
    simp

theorem criticalSq_zero : criticalSq zeroDatum = 0 := by
  simp [criticalSq, zeroDatum, hhalfSq, hhalfTerm]

theorem zero_small {ν C3 : ℝ}
    (hν : 0 < ν) (hC3 : 0 < C3) :
    Small ν C3 zeroDatum := by
  refine ⟨hν, hC3, ?_⟩
  rw [criticalSq_zero]
  exact sq_pos_of_pos (smallRadius_pos hν hC3)

def zeroSmallDatum (ν C3 : ℝ)
    (hν : 0 < ν) (hC3 : 0 < C3) : SmallDatum ν C3 :=
  ⟨zeroDatum, zero_small hν hC3⟩

theorem heatCoeff_reality (ν t : ℝ) (a : Mode3 → CVec3)
    (ha : ConjugateReality a) :
    ConjugateReality (heatCoeff ν t a) := by
  intro k i
  change
    ((heatFactor ν t (-k) : ℝ) : ℂ) * a (-k) i =
      star (((heatFactor ν t k : ℝ) : ℂ) * a k i)
  have hf : heatFactor ν t (-k) = heatFactor ν t k := by
    simp only [heatFactor, freq_neg]
  rw [hf, ha k i]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]

/-- Heat evolution in the concrete real Fourier carrier. -/
def heatRealDatum (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : RealH12Datum) : RealH12Datum where
  toH12Datum := heatDatum ν t hν ht a.toH12Datum
  reality := heatCoeff_reality ν t a.coeff a.reality

theorem heat_criticalSq_le (ν t : ℝ)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) (a : RealH12Datum) :
    criticalSq (heatRealDatum ν t hν ht a) ≤ criticalSq a := by
  exact heat_hhalfSq_le hν ht a.toH12Datum

theorem heat_preserves_small {ν C3 t : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (ht : 0 ≤ t) :
    Small ν C3 (heatRealDatum ν t ha.1.le ht a) := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  exact (heat_criticalSq_le ν t ha.1.le ht a).trans_lt ha.2.2

def heatSmallDatum {ν C3 : ℝ} (a : SmallDatum ν C3)
    (t : ℝ) (ht : 0 ≤ t) : SmallDatum ν C3 :=
  ⟨heatRealDatum ν t a.property.1.le ht a.val,
    heat_preserves_small a.val a.property ht⟩

/-- A finite Fourier cutoff; no closure under the nonlinear evolution is asserted. -/
def cutoffCoeff (S : Finset Mode3) (a : Mode3 → CVec3)
    (k : Mode3) : CVec3 :=
  if k ∈ S then a k else 0

theorem cutoffCoeff_outside (S : Finset Mode3) (a : Mode3 → CVec3)
    (k : Mode3) (hk : k ∉ S) :
    cutoffCoeff S a k = 0 := by
  simp [cutoffCoeff, hk]

theorem hhalfTerm_cutoff_le (S : Finset Mode3)
    (a : Mode3 → CVec3) (k : Mode3) :
    hhalfTerm (cutoffCoeff S a) k ≤ hhalfTerm a k := by
  classical
  by_cases hk : k ∈ S
  · simp [hhalfTerm, cutoffCoeff, hk]
  · simpa [hhalfTerm, cutoffCoeff, hk] using hhalfTerm_nonneg a k

/-- The complex critical datum construction works for every finite cutoff. -/
def cutoffDatum (S : Finset Mode3) (a : H12Datum) : H12Datum where
  coeff := cutoffCoeff S a.coeff
  meanZero := by
    simp [cutoffCoeff, a.meanZero]
  solenoidal := by
    intro k
    classical
    by_cases hk : k ∈ S
    · simpa [cutoffCoeff, hk] using a.solenoidal k
    · change cutoffCoeff S a.coeff k ∈ solenoidalSubmodule k
      rw [cutoffCoeff_outside S a.coeff k hk]
      exact (solenoidalSubmodule k).zero_mem
  hhalfSummable := by
    exact Summable.of_nonneg_of_le
      (fun k => hhalfTerm_nonneg (cutoffCoeff S a.coeff) k)
      (fun k => hhalfTerm_cutoff_le S a.coeff k)
      a.hhalfSummable

/-- Negation invariance is exactly the cutoff hypothesis preserving reality. -/
def SymmetricCutoff (S : Finset Mode3) : Prop :=
  ∀ k : Mode3, -k ∈ S ↔ k ∈ S

theorem cutoffCoeff_reality (S : Finset Mode3)
    (hS : SymmetricCutoff S) (a : Mode3 → CVec3)
    (ha : ConjugateReality a) :
    ConjugateReality (cutoffCoeff S a) := by
  intro k i
  classical
  by_cases hk : k ∈ S
  · have hneg : -k ∈ S := (hS k).2 hk
    simpa [cutoffCoeff, hk, hneg] using ha k i
  · have hneg : -k ∉ S := by
      intro h
      exact hk ((hS k).1 h)
    simp [cutoffCoeff, hk, hneg]

def cutoffRealDatum (S : Finset Mode3) (hS : SymmetricCutoff S)
    (a : RealH12Datum) : RealH12Datum where
  toH12Datum := cutoffDatum S a.toH12Datum
  reality := cutoffCoeff_reality S hS a.coeff a.reality

theorem cutoff_criticalSq_le (S : Finset Mode3)
    (hS : SymmetricCutoff S) (a : RealH12Datum) :
    criticalSq (cutoffRealDatum S hS a) ≤ criticalSq a := by
  exact (cutoffDatum S a.toH12Datum).hhalfSummable.tsum_le_tsum
    (fun k => hhalfTerm_cutoff_le S a.coeff k)
    a.hhalfSummable

theorem cutoff_preserves_small {ν C3 : ℝ}
    (S : Finset Mode3) (hS : SymmetricCutoff S)
    (a : RealH12Datum) (ha : Small ν C3 a) :
    Small ν C3 (cutoffRealDatum S hS a) := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  exact (cutoff_criticalSq_le S hS a).trans_lt ha.2.2

def cutoffSmallDatum {ν C3 : ℝ}
    (S : Finset Mode3) (hS : SymmetricCutoff S)
    (a : SmallDatum ν C3) : SmallDatum ν C3 :=
  ⟨cutoffRealDatum S hS a.val,
    cutoff_preserves_small S hS a.val a.property⟩

/--
Exact carrier endpoint: nonvacuity together with heat and symmetric-cutoff
preservation.  This proposition does not contain a global NSE regularity
conclusion or an implicit evolution certificate.
-/
theorem H12_SIGMA_ZERO_SMALL_CLASS :
    (∀ (ν C3 : ℝ), 0 < ν → 0 < C3 → Nonempty (SmallDatum ν C3)) ∧
    (∀ {ν C3 t : ℝ} (a : RealH12Datum) (ha : Small ν C3 a)
      (ht : 0 ≤ t), Small ν C3 (heatRealDatum ν t ha.1.le ht a)) ∧
    (∀ {ν C3 : ℝ} (S : Finset Mode3) (hS : SymmetricCutoff S)
      (a : RealH12Datum), Small ν C3 a →
        Small ν C3 (cutoffRealDatum S hS a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ν C3 hν hC3
    exact ⟨zeroSmallDatum ν C3 hν hC3⟩
  · intro ν C3 t a ha ht
    exact heat_preserves_small a ha ht
  · intro ν C3 S hS a ha
    exact cutoff_preserves_small S hS a ha

end H12SigmaZeroSmallClass
