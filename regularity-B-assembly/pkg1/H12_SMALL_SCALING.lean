import H12_SIGMA_ZERO_SMALL_CLASS

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace H12SmallScaling

open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass

/-- Real scalar multiplication of the actual complex Fourier coefficients. -/
def scaleCoeff (r : ℝ) (a : Mode3 → CVec3) (k : Mode3) : CVec3 :=
  (r : ℂ) • a k

theorem scaleCoeff_reality (r : ℝ) (a : Mode3 → CVec3)
    (ha : ConjugateReality a) :
    ConjugateReality (scaleCoeff r a) := by
  intro k i
  change (r : ℂ) * a (-k) i = star ((r : ℂ) * a k i)
  rw [ha k i]
  simp [mul_comm]

theorem hhalfTerm_scale (r : ℝ) (a : Mode3 → CVec3) (k : Mode3) :
    hhalfTerm (scaleCoeff r a) k = r ^ 2 * hhalfTerm a k := by
  have hnorm : ‖scaleCoeff r a k‖ = |r| * ‖a k‖ := by
    simp [scaleCoeff, norm_smul]
  rw [hhalfTerm, hhalfTerm, hnorm, mul_pow, sq_abs]
  ring

/-- Real scaling preserves mean zero, solenoidality, summability and reality. -/
def scaleDatum (r : ℝ) (a : RealH12Datum) : RealH12Datum where
  coeff := scaleCoeff r a.coeff
  meanZero := by
    simp [scaleCoeff, a.meanZero]
  solenoidal := by
    intro k
    exact (solenoidalSubmodule k).smul_mem (r : ℂ) (a.solenoidal k)
  hhalfSummable := by
    change Summable (fun k : Mode3 => hhalfTerm (scaleCoeff r a.coeff) k)
    simp_rw [hhalfTerm_scale]
    exact a.hhalfSummable.mul_left (r ^ 2)
  reality := scaleCoeff_reality r a.coeff a.reality

theorem criticalSq_scale (r : ℝ) (a : RealH12Datum) :
    criticalSq (scaleDatum r a) = r ^ 2 * criticalSq a := by
  change (∑' k : Mode3, hhalfTerm (scaleCoeff r a.coeff) k) =
    r ^ 2 * ∑' k : Mode3, hhalfTerm a.coeff k
  simp_rw [hhalfTerm_scale]
  rw [tsum_mul_left]

theorem criticalNorm_scale (r : ℝ) (a : RealH12Datum) :
    criticalNorm (scaleDatum r a) = |r| * criticalNorm a := by
  change Real.sqrt (criticalSq (scaleDatum r a)) =
    |r| * Real.sqrt (criticalSq a)
  rw [criticalSq_scale, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

theorem scale_preserves_small {ν C3 r : ℝ}
    (a : RealH12Datum) (ha : Small ν C3 a) (hr : |r| ≤ 1) :
    Small ν C3 (scaleDatum r a) := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  rw [criticalSq_scale]
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg r, sq_abs r]
  have hle : r ^ 2 * criticalSq a ≤ criticalSq a := by
    simpa using mul_le_mul_of_nonneg_right hr2 (criticalSq_nonneg a)
  exact hle.trans_lt ha.2.2

def scaleSmallDatum {ν C3 : ℝ} (r : ℝ) (hr : |r| ≤ 1)
    (a : SmallDatum ν C3) : SmallDatum ν C3 :=
  ⟨scaleDatum r a.val, scale_preserves_small a.val a.property hr⟩

theorem small_of_norm_lt {ν C3 : ℝ} (a : RealH12Datum)
    (hν : 0 < ν) (hC3 : 0 < C3)
    (ha : criticalNorm a < smallRadius ν C3) : Small ν C3 a := by
  refine ⟨hν, hC3, ?_⟩
  have hr := smallRadius_pos hν hC3
  have hn := criticalNorm_nonneg a
  have hs := criticalNorm_sq a
  have hp : 0 < (smallRadius ν C3 - criticalNorm a) *
      (smallRadius ν C3 + criticalNorm a) := by
    apply mul_pos (sub_pos.mpr ha)
    linarith
  nlinarith

/-- Every fixed real critical datum has arbitrarily small positive admissible multiples. -/
theorem exists_small_positive_scale (ν C3 ε : ℝ)
    (hν : 0 < ν) (hC3 : 0 < C3) (hε : 0 < ε)
    (a : RealH12Datum) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ Small ν C3 (scaleDatum r a) := by
  let R : ℝ := smallRadius ν C3
  let E : ℝ := criticalNorm a
  let r : ℝ := min (ε / 2) (R / (2 * (E + 1)))
  have hR : 0 < R := smallRadius_pos hν hC3
  have hE : 0 ≤ E := criticalNorm_nonneg a
  have hd : 0 < 2 * (E + 1) := by linarith
  have hr : 0 < r := by
    exact lt_min (by linarith) (div_pos hR hd)
  have hrε : r < ε := by
    exact (min_le_left (ε / 2) (R / (2 * (E + 1)))).trans_lt (by linarith)
  have hbound : r ≤ R / (2 * (E + 1)) := min_le_right _ _
  have hmul : r * (2 * (E + 1)) ≤ R := (le_div_iff₀ hd).mp hbound
  have hprod : r * E < R := by nlinarith
  refine ⟨r, hr, hrε, small_of_norm_lt (scaleDatum r a) hν hC3 ?_⟩
  rw [criticalNorm_scale, abs_of_pos hr]
  exact hprod

theorem scaleDatum_coeff_ne_zero (r : ℝ) (hr : r ≠ 0)
    (a : RealH12Datum) (ha : a.coeff ≠ 0) :
    (scaleDatum r a).coeff ≠ 0 := by
  intro h
  apply ha
  funext k
  have hk : (r : ℂ) • a.coeff k = 0 := congrFun h k
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  exact (smul_eq_zero.mp hk).resolve_left hrC

/-- One nonzero frequency, along the first coordinate. -/
def baseMode : Mode3 :=
  fun i => if i = 0 then 1 else 0

/-- A real unit polarization transverse to `baseMode`. -/
def transverseVector : CVec3 :=
  EuclideanSpace.single (1 : Fin 3) (1 : ℂ)

theorem baseMode_ne_zero : baseMode ≠ 0 := by
  intro h
  have h0 := congrArg (fun k : Mode3 => k (0 : Fin 3)) h
  norm_num [baseMode] at h0

theorem transverseVector_reality (i : Fin 3) :
    transverseVector i = star (transverseVector i) := by
  simp [transverseVector, PiLp.single_apply]

theorem transverseVector_solenoidal (k : Mode3)
    (hk : k (1 : Fin 3) = 0) : SolenoidalAt k transverseVector := by
  change inner ℂ (modeComplex k)
    (EuclideanSpace.single (1 : Fin 3) (1 : ℂ)) = 0
  rw [EuclideanSpace.inner_single_right]
  simp [modeComplex, hk]

/-- Explicit two-mode real cosine datum; coefficients vanish outside `{k,-k}`. -/
def twoModeCoeff (k : Mode3) : CVec3 :=
  if k = baseMode ∨ k = -baseMode then transverseVector else 0

theorem twoModeCoeff_reality : ConjugateReality twoModeCoeff := by
  intro k i
  have hsym : (-k = baseMode ∨ -k = -baseMode) ↔
      (k = baseMode ∨ k = -baseMode) := by
    constructor
    · rintro (h | h)
      · right
        simpa using congrArg Neg.neg h
      · left
        simpa using congrArg Neg.neg h
    · rintro (h | h)
      · right
        rw [h]
      · left
        rw [h, neg_neg]
  by_cases hk : k = baseMode ∨ k = -baseMode
  · have hn := hsym.mpr hk
    simpa [twoModeCoeff, hk, hn] using transverseVector_reality i
  · have hn : ¬(-k = baseMode ∨ -k = -baseMode) := by
      exact fun h => hk (hsym.mp h)
    simp [twoModeCoeff, hk, hn]

def twoModeDatum : RealH12Datum where
  coeff := twoModeCoeff
  meanZero := by
    have h0 : (0 : Mode3) ≠ baseMode := Ne.symm baseMode_ne_zero
    have hn : (0 : Mode3) ≠ -baseMode := Ne.symm (neg_ne_zero.mpr baseMode_ne_zero)
    simp [twoModeCoeff, h0, hn]
  solenoidal := by
    intro k
    by_cases hk : k = baseMode ∨ k = -baseMode
    · have hk1 : k (1 : Fin 3) = 0 := by
        rcases hk with h | h
        · rw [h]
          norm_num [baseMode]
        · rw [h]
          norm_num [baseMode]
      simpa [twoModeCoeff, hk] using transverseVector_solenoidal k hk1
    · change twoModeCoeff k ∈ solenoidalSubmodule k
      simp only [twoModeCoeff, if_neg hk]
      exact (solenoidalSubmodule k).zero_mem
  hhalfSummable := by
    apply summable_of_ne_finset_zero (s := {baseMode, -baseMode})
    intro k hk
    have hnot : ¬(k = baseMode ∨ k = -baseMode) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hk
    simp [hhalfTerm, twoModeCoeff, hnot]
  reality := twoModeCoeff_reality

theorem twoModeDatum_coeff_ne_zero : twoModeDatum.coeff ≠ 0 := by
  intro h
  have hc := congrArg
    (fun f : Mode3 → CVec3 => f baseMode (1 : Fin 3)) h
  norm_num [twoModeDatum, twoModeCoeff, transverseVector, PiLp.single_apply] at hc

/-- The small carrier contains an actual nonzero finitely supported datum. -/
theorem exists_nonzero_small (ν C3 : ℝ)
    (hν : 0 < ν) (hC3 : 0 < C3) :
    ∃ a : SmallDatum ν C3, a.val.coeff ≠ 0 := by
  obtain ⟨r, hr, _, hs⟩ :=
    exists_small_positive_scale ν C3 1 hν hC3 (by norm_num) twoModeDatum
  exact ⟨⟨scaleDatum r twoModeDatum, hs⟩,
    scaleDatum_coeff_ne_zero r (ne_of_gt hr) twoModeDatum twoModeDatum_coeff_ne_zero⟩

/-- Exact coefficient-level scaling and nonzero-admission endpoint. -/
theorem H12_SMALL_SCALING :
    (∀ (r : ℝ) (a : RealH12Datum),
      criticalSq (scaleDatum r a) = r ^ 2 * criticalSq a) ∧
    (∀ {ν C3 r : ℝ} (a : RealH12Datum),
      Small ν C3 a → |r| ≤ 1 → Small ν C3 (scaleDatum r a)) ∧
    (∀ (ν C3 : ℝ), 0 < ν → 0 < C3 →
      ∃ a : SmallDatum ν C3, a.val.coeff ≠ 0) := by
  exact ⟨criticalSq_scale, scale_preserves_small, exists_nonzero_small⟩

end H12SmallScaling
