import SingularClosure.TorusGalerkinSobolev
import SingularClosure.PeriodicPoincare

/-! Actual homogeneous Fourier Sobolev spaces in half-integer orders.
The integer index q denotes H^(q/2). The zero frequency has weight one;
on nonzero frequencies the squared frequency weight is the actual Laplace
symbol. Mean-zero inputs therefore have exactly the homogeneous norms.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

/-- Homogeneous unit-period frequency weight, completed positively at zero. -/
def criticalFrequencyWeight (k : Frequency) : ℝ :=
  if k = 0 then 1 else Real.sqrt (laplacianFrequency k)

theorem laplacianFrequency_nonneg (k : Frequency) : 0 ≤ laplacianFrequency k := by
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  exact mul_nonneg (sq_nonneg (2 * Real.pi)) hk

@[simp]
theorem criticalFrequencyWeight_zero : criticalFrequencyWeight 0 = 1 := by
  simp [criticalFrequencyWeight]

theorem criticalFrequencyWeight_one_le (k : Frequency) : 1 ≤ criticalFrequencyWeight k := by
  classical
  by_cases hk : k = 0
  · simp [criticalFrequencyWeight, hk]
  · have hfreq : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
      exact_mod_cast galerkinFreqSq_ge_one_of_ne_zero k hk
    have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hlap : 1 ≤ laplacianFrequency k := by
      unfold laplacianFrequency
      nlinarith [mul_le_mul_of_nonneg_left hfreq (sq_nonneg (2 * Real.pi))]
    rw [criticalFrequencyWeight, if_neg hk]
    apply (Real.le_sqrt (by norm_num) (laplacianFrequency_nonneg k)).mpr
    simpa only [one_pow] using hlap

theorem criticalFrequencyWeight_pos (k : Frequency) : 0 < criticalFrequencyWeight k :=
  lt_of_lt_of_le zero_lt_one (criticalFrequencyWeight_one_le k)

theorem criticalFrequencyWeight_sq_of_ne_zero (k : Frequency) (hk : k ≠ 0) :
    criticalFrequencyWeight k ^ 2 = laplacianFrequency k := by
  rw [criticalFrequencyWeight, if_neg hk]
  exact Real.sq_sqrt (laplacianFrequency_nonneg k)

/-- One half of a Sobolev derivative in the weighted coordinates. -/
def criticalHalfWeight (k : Frequency) : ℝ := Real.sqrt (criticalFrequencyWeight k)

theorem criticalHalfWeight_pos (k : Frequency) : 0 < criticalHalfWeight k :=
  Real.sqrt_pos.mpr (criticalFrequencyWeight_pos k)

theorem criticalHalfWeight_one_le (k : Frequency) : 1 ≤ criticalHalfWeight k := by
  apply (Real.le_sqrt (by norm_num) (criticalFrequencyWeight_pos k).le).mpr
  simpa only [one_pow] using criticalFrequencyWeight_one_le k

theorem criticalHalfWeight_sq (k : Frequency) :
    criticalHalfWeight k ^ 2 = criticalFrequencyWeight k :=
  Real.sq_sqrt (criticalFrequencyWeight_pos k).le

theorem criticalHalfWeight_complex_ne_zero (k : Frequency) :
    (criticalHalfWeight k : ℂ) ≠ 0 := by
  exact_mod_cast (criticalHalfWeight_pos k).ne'

theorem criticalHalfWeight_zpow_sq (q : ℤ) (k : Frequency) :
    (criticalHalfWeight k ^ q) ^ 2 = criticalFrequencyWeight k ^ q := by
  rw [pow_two, ← mul_zpow, ← pow_two, criticalHalfWeight_sq]

/-- The literal weighted Fourier coordinates for order q/2. -/
def criticalWeightedCoeff (q : ℤ) (c : FourierCoeff) (ki : FourierIndex) : ℂ :=
  (criticalHalfWeight ki.1 : ℂ) ^ q * c ki.1 ki.2

theorem criticalWeightedCoeff_zero (q : ℤ) : criticalWeightedCoeff q 0 = 0 := by
  funext ki
  simp [criticalWeightedCoeff]

theorem criticalWeightedCoeff_add (q : ℤ) (c d : FourierCoeff) :
    criticalWeightedCoeff q (c + d) = criticalWeightedCoeff q c + criticalWeightedCoeff q d := by
  funext ki
  exact mul_add _ _ _

theorem criticalWeightedCoeff_smul (q : ℤ) (z : ℂ) (c : FourierCoeff) :
    criticalWeightedCoeff q (z • c) = z • criticalWeightedCoeff q c := by
  funext ki
  exact mul_left_comm _ _ _

theorem criticalWeightedCoeff_norm (q : ℤ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖criticalWeightedCoeff q c ki‖ =
      criticalHalfWeight ki.1 ^ q * ‖c ki.1 ki.2‖ := by
  simp only [criticalWeightedCoeff, norm_mul, norm_zpow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (criticalHalfWeight_pos ki.1)]

def criticalSobolevSubmodule (q : ℤ) : Submodule ℂ FourierCoeff where
  carrier := {c | Memℓp (criticalWeightedCoeff q c) 2}
  zero_mem' := by
    change Memℓp (criticalWeightedCoeff q 0) 2
    rw [criticalWeightedCoeff_zero]
    exact zero_memℓp
  add_mem' := by
    intro c d hc hd
    change Memℓp (criticalWeightedCoeff q (c + d)) 2
    rw [criticalWeightedCoeff_add]
    exact hc.add hd
  smul_mem' := by
    intro z c hc
    change Memℓp (criticalWeightedCoeff q (z • c)) 2
    rw [criticalWeightedCoeff_smul]
    exact hc.const_smul z

/-- Actual coefficient arrays of Sobolev order q/2. -/
def CriticalSobolev (q : ℤ) : Type :=
  {c : FourierCoeff // Memℓp (criticalWeightedCoeff q c) 2}

instance criticalSobolevAddCommGroup (q : ℤ) : AddCommGroup (CriticalSobolev q) :=
  inferInstanceAs (AddCommGroup ↥(criticalSobolevSubmodule q))

instance criticalSobolevModule (q : ℤ) : Module ℂ (CriticalSobolev q) :=
  inferInstanceAs (Module ℂ ↥(criticalSobolevSubmodule q))

/-- Raw Fourier coefficients; this map is independent of norm-instance reduction. -/
def criticalCoeff (q : ℤ) (c : CriticalSobolev q) : FourierCoeff := c.val

@[simp]
theorem criticalCoeff_zero (q : ℤ) : criticalCoeff q 0 = 0 := rfl

@[simp]
theorem criticalCoeff_add (q : ℤ) (c d : CriticalSobolev q) :
    criticalCoeff q (c + d) = criticalCoeff q c + criticalCoeff q d := rfl

@[simp]
theorem criticalCoeff_smul (q : ℤ) (z : ℂ) (c : CriticalSobolev q) :
    criticalCoeff q (z • c) = z • criticalCoeff q c := rfl

theorem criticalCoeff_mem (q : ℤ) (c : CriticalSobolev q) :
    Memℓp (criticalWeightedCoeff q (criticalCoeff q c)) 2 := c.property

theorem criticalCoeff_injective (q : ℤ) : Function.Injective (criticalCoeff q) := by
  intro c d h
  exact Subtype.ext h

def criticalSobolevReprLinear (q : ℤ) : CriticalSobolev q →ₗ[ℂ] FourierVectorSequence where
  toFun c := ⟨criticalWeightedCoeff q (criticalCoeff q c), criticalCoeff_mem q c⟩
  map_add' c d := by
    apply lp.ext
    exact criticalWeightedCoeff_add q (criticalCoeff q c) (criticalCoeff q d)
  map_smul' z c := by
    apply lp.ext
    exact criticalWeightedCoeff_smul q z (criticalCoeff q c)

@[simp]
theorem criticalSobolevReprLinear_apply (q : ℤ) (c : CriticalSobolev q) (ki : FourierIndex) :
    criticalSobolevReprLinear q c ki = criticalWeightedCoeff q (criticalCoeff q c) ki := rfl

theorem criticalSobolevReprLinear_injective (q : ℤ) :
    Function.Injective (criticalSobolevReprLinear q) := by
  intro c d h
  apply criticalCoeff_injective q
  funext k i
  have hki := congrArg (fun z : FourierVectorSequence => z (k, i)) h
  exact mul_left_cancel₀ (zpow_ne_zero q (criticalHalfWeight_complex_ne_zero k)) hki

theorem criticalSobolevReprLinear_surjective (q : ℤ) :
    Function.Surjective (criticalSobolevReprLinear q) := by
  intro z
  let c : FourierCoeff := fun k i => z (k, i) / (criticalHalfWeight k : ℂ) ^ q
  have hc : criticalWeightedCoeff q c = (z : FourierIndex → ℂ) := by
    funext ki
    dsimp only [criticalWeightedCoeff, c]
    have hw : (criticalHalfWeight ki.1 : ℂ) ^ q ≠ 0 :=
      zpow_ne_zero q (criticalHalfWeight_complex_ne_zero ki.1)
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hw, mul_one]
  refine ⟨⟨c, ?_⟩, ?_⟩
  · change Memℓp (criticalWeightedCoeff q c) 2
    rw [hc]
    exact lp.memℓp z
  · apply lp.ext
    exact hc

instance criticalSobolevNormedAddCommGroup (q : ℤ) : NormedAddCommGroup (CriticalSobolev q) :=
  NormedAddCommGroup.induced _ _ (criticalSobolevReprLinear q)
    (criticalSobolevReprLinear_injective q)

instance criticalSobolevInnerProductSpace (q : ℤ) : InnerProductSpace ℂ (CriticalSobolev q) :=
  InnerProductSpace.induced (criticalSobolevReprLinear q)

def criticalSobolevRepr (q : ℤ) : CriticalSobolev q ≃ₗᵢ[ℂ] FourierVectorSequence where
  __ := LinearEquiv.ofBijective (criticalSobolevReprLinear q)
    ⟨criticalSobolevReprLinear_injective q, criticalSobolevReprLinear_surjective q⟩
  norm_map' _ := rfl

@[simp]
theorem criticalSobolevRepr_apply (q : ℤ) (c : CriticalSobolev q) (ki : FourierIndex) :
    criticalSobolevRepr q c ki = criticalWeightedCoeff q (criticalCoeff q c) ki := rfl

instance criticalSobolevCompleteSpace (q : ℤ) : CompleteSpace (CriticalSobolev q) :=
  (criticalSobolevRepr q).toIsometryEquiv.completeSpace_iff.mpr inferInstance

instance criticalSobolevNormedSpaceReal (q : ℤ) : NormedSpace ℝ (CriticalSobolev q) :=
  NormedSpace.restrictScalars ℝ ℂ (CriticalSobolev q)

instance criticalSobolevRealScalarTower (q : ℤ) : IsScalarTower ℝ ℂ (CriticalSobolev q) :=
  Real.isScalarTower

/-- A membership proof produces the literal coefficient array, with no existence premise. -/
theorem exists_criticalSobolevOfCoeff (q : ℤ) (c : FourierCoeff)
    (hc : Memℓp (criticalWeightedCoeff q c) 2) :
    ∃ u : CriticalSobolev q, criticalCoeff q u = c :=
  ⟨⟨c, hc⟩, Eq.refl c⟩

def criticalSobolevOfCoeff (q : ℤ) (c : FourierCoeff)
    (hc : Memℓp (criticalWeightedCoeff q c) 2) : CriticalSobolev q :=
  (exists_criticalSobolevOfCoeff q c hc).choose

@[simp]
theorem criticalSobolevOfCoeff_coeff (q : ℤ) (c : FourierCoeff)
    (hc : Memℓp (criticalWeightedCoeff q c) 2) :
    criticalCoeff q (criticalSobolevOfCoeff q c hc) = c :=
  (exists_criticalSobolevOfCoeff q c hc).choose_spec

theorem criticalSobolev_norm_sq (q : ℤ) (c : CriticalSobolev q) :
    ‖c‖ ^ 2 = ∑' ki : FourierIndex,
      criticalFrequencyWeight ki.1 ^ q * Complex.normSq (criticalCoeff q c ki.1 ki.2) := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (criticalSobolevRepr q c)
  have h' : ‖c‖ ^ 2 = ∑' ki : FourierIndex,
      ‖criticalWeightedCoeff q (criticalCoeff q c) ki‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      (criticalSobolevRepr q).norm_map, criticalSobolevRepr_apply] using h
  rw [h']
  apply tsum_congr
  intro ki
  rw [criticalWeightedCoeff_norm, mul_pow, criticalHalfWeight_zpow_sq,
    Complex.normSq_eq_norm_sq]

/-- Exact complex Fourier evaluation as a continuous linear functional. -/
def criticalSobolevCoeff (q : ℤ) (k : Frequency) (i : Fin 3) :
    CriticalSobolev q →L[ℂ] ℂ :=
  ((criticalHalfWeight k : ℂ) ^ q)⁻¹ •
    ((lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 (k, i)).comp
      (criticalSobolevRepr q).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem criticalSobolevCoeff_apply (q : ℤ) (c : CriticalSobolev q)
    (k : Frequency) (i : Fin 3) : criticalSobolevCoeff q k i c = criticalCoeff q c k i := by
  change ((criticalHalfWeight k : ℂ) ^ q)⁻¹ *
    criticalWeightedCoeff q (criticalCoeff q c) (k, i) = _
  unfold criticalWeightedCoeff
  rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero q (criticalHalfWeight_complex_ne_zero k)), one_mul]

theorem criticalCoeff_continuous (q : ℤ) (k : Frequency) (i : Fin 3) :
    Continuous (fun c : CriticalSobolev q => criticalCoeff q c k i) := by
  have hfun : (criticalSobolevCoeff q k i : CriticalSobolev q → ℂ) =
      (fun c : CriticalSobolev q => criticalCoeff q c k i) := by
    funext c
    exact criticalSobolevCoeff_apply q c k i
  rw [← hfun]
  exact (criticalSobolevCoeff q k i).continuous

end

end SingularClosure
