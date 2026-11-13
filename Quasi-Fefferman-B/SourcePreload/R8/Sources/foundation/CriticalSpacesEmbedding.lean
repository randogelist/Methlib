import SingularClosure.CriticalSpacesCutoff
import SingularClosure.SobolevL2Realization

/-! Coefficient-preserving embeddings and actual physical L² realization. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

theorem criticalWeightedCoeff_norm_mono {q r : ℤ} (hqr : q ≤ r)
    (c : FourierCoeff) (ki : FourierIndex) :
    ‖criticalWeightedCoeff q c ki‖ ≤ ‖criticalWeightedCoeff r c ki‖ := by
  rw [criticalWeightedCoeff_norm, criticalWeightedCoeff_norm]
  exact mul_le_mul_of_nonneg_right
    (zpow_le_zpow_right₀ (criticalHalfWeight_one_le ki.1) hqr) (norm_nonneg _)

theorem criticalSobolevLower_mem (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    Memℓp (criticalWeightedCoeff q (criticalCoeff r c)) 2 :=
  (criticalCoeff_mem r c).mono' (criticalWeightedCoeff_norm_mono hqr (criticalCoeff r c))

def criticalSobolevLowerValue (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    CriticalSobolev q :=
  criticalSobolevOfCoeff q (criticalCoeff r c) (criticalSobolevLower_mem q r hqr c)

@[simp]
theorem criticalSobolevLowerValue_coeff (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    criticalCoeff q (criticalSobolevLowerValue q r hqr c) = criticalCoeff r c :=
  criticalSobolevOfCoeff_coeff q (criticalCoeff r c) (criticalSobolevLower_mem q r hqr c)

def criticalSobolevLowerLinear (q r : ℤ) (hqr : q ≤ r) :
    CriticalSobolev r →ₗ[ℂ] CriticalSobolev q where
  toFun := criticalSobolevLowerValue q r hqr
  map_add' c d := by
    apply criticalCoeff_injective q
    simp only [criticalSobolevLowerValue_coeff, criticalCoeff_add]
  map_smul' z c := by
    apply criticalCoeff_injective q
    simp only [criticalSobolevLowerValue_coeff, criticalCoeff_smul, RingHom.id_apply]

@[simp]
theorem criticalSobolevLowerLinear_coeff (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    criticalCoeff q (criticalSobolevLowerLinear q r hqr c) = criticalCoeff r c :=
  criticalSobolevLowerValue_coeff q r hqr c

theorem criticalSobolevLowerLinear_norm_le (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    ‖criticalSobolevLowerLinear q r hqr c‖ ≤ ‖c‖ := by
  calc
    _ = ‖criticalSobolevRepr q (criticalSobolevLowerLinear q r hqr c)‖ :=
      ((criticalSobolevRepr q).norm_map _).symm
    _ ≤ ‖criticalSobolevRepr r c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [criticalSobolevRepr_apply, criticalSobolevLowerLinear_coeff]
      exact criticalWeightedCoeff_norm_mono hqr (criticalCoeff r c) ki
    _ = ‖c‖ := (criticalSobolevRepr r).norm_map c

theorem criticalSobolevLower_bound (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    ‖criticalSobolevLowerLinear q r hqr c‖ ≤ 1 * ‖c‖ := by
  simpa only [one_mul] using criticalSobolevLowerLinear_norm_le q r hqr c

/-- The literal same coefficient array, in a lower half-order norm. -/
def criticalSobolevLower (q r : ℤ) (hqr : q ≤ r) :
    CriticalSobolev r →L[ℂ] CriticalSobolev q :=
  (criticalSobolevLowerLinear q r hqr).mkContinuous 1 (criticalSobolevLower_bound q r hqr)

@[simp]
theorem criticalSobolevLower_coeff (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    criticalCoeff q (criticalSobolevLower q r hqr c) = criticalCoeff r c := by
  unfold criticalSobolevLower
  exact (congrArg (criticalCoeff q)
    ((criticalSobolevLowerLinear q r hqr).mkContinuous_apply 1
      (criticalSobolevLower_bound q r hqr) c)).trans
    (criticalSobolevLowerLinear_coeff q r hqr c)

theorem criticalSobolevLower_norm_le (q r : ℤ) (hqr : q ≤ r) (c : CriticalSobolev r) :
    ‖criticalSobolevLower q r hqr c‖ ≤ ‖c‖ := criticalSobolevLowerLinear_norm_le q r hqr c

/-- At order zero both concrete Fourier Hilbert spaces agree isometrically. -/
def criticalH0Equiv : CriticalSobolev 0 ≃ₗᵢ[ℂ] TorusSobolev 0 :=
  (criticalSobolevRepr 0).trans (torusSobolevRepr 0).symm

@[simp]
theorem criticalH0Equiv_coeff (c : CriticalSobolev 0) :
    (criticalH0Equiv c).val = criticalCoeff 0 c := by
  funext k i
  have h := congrArg (fun z : FourierVectorSequence => z (k, i))
    ((torusSobolevRepr 0).apply_symm_apply (criticalSobolevRepr 0 c))
  simpa only [criticalH0Equiv, LinearIsometryEquiv.trans_apply,
    torusSobolevRepr_apply, criticalSobolevRepr_apply, criticalWeightedCoeff,
    pow_zero, zpow_zero, one_mul] using h

/-- Every nonnegative half-order input has a literal order-zero Fourier image. -/
def criticalToTorusH0 (q : ℤ) (hq : 0 ≤ q) : CriticalSobolev q →L[ℂ] TorusSobolev 0 :=
  criticalH0Equiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (criticalSobolevLower 0 q hq)

@[simp]
theorem criticalToTorusH0_coeff (q : ℤ) (hq : 0 ≤ q) (c : CriticalSobolev q) :
    (criticalToTorusH0 q hq c).val = criticalCoeff q c := by
  change (criticalH0Equiv (criticalSobolevLower 0 q hq c)).val = _
  rw [criticalH0Equiv_coeff, criticalSobolevLower_coeff]

theorem criticalToTorusH0_norm_le (q : ℤ) (hq : 0 ≤ q) (c : CriticalSobolev q) :
    ‖criticalToTorusH0 q hq c‖ ≤ ‖c‖ := by
  change ‖criticalH0Equiv (criticalSobolevLower 0 q hq c)‖ ≤ _
  rw [criticalH0Equiv.norm_map]
  exact criticalSobolevLower_norm_le 0 q hq c

/-- Comparison with the existing inhomogeneous integer Sobolev weight. -/
theorem torusSobolevWeight_le_two_criticalFrequencyWeight (k : Frequency) :
    torusSobolevWeight k ≤ 2 * criticalFrequencyWeight k := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [torusSobolevWeight, criticalFrequencyWeight, galerkinFreqSq]
  · have hw := criticalFrequencyWeight_one_le k
    have hsq := criticalFrequencyWeight_sq_of_ne_zero k hk
    have ht := torusSobolevWeight_sq k
    have hpos := torusSobolevWeight_pos k
    change criticalFrequencyWeight k ^ 2 =
      (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) at hsq
    apply (sq_le_sq₀ hpos.le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (criticalFrequencyWeight_pos k).le)).mp
    nlinarith

theorem torusSobolevWeight_le_two_criticalHalfWeight_cube (k : Frequency) :
    torusSobolevWeight k ≤ 2 * criticalHalfWeight k ^ 3 := by
  have hw : criticalFrequencyWeight k ≤ criticalHalfWeight k ^ 3 := by
    rw [← criticalHalfWeight_sq]
    exact pow_le_pow_right₀ (criticalHalfWeight_one_le k) (by norm_num : 2 ≤ 3)
  exact (torusSobolevWeight_le_two_criticalFrequencyWeight k).trans
    (mul_le_mul_of_nonneg_left hw (by norm_num))

theorem criticalToTorusH1_weighted_bound (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff 1 c ki‖ ≤ 2 * ‖criticalWeightedCoeff 3 c ki‖ := by
  have h := mul_le_mul_of_nonneg_right
    (torusSobolevWeight_le_two_criticalHalfWeight_cube ki.1) (norm_nonneg (c ki.1 ki.2))
  simpa only [criticalWeightedCoeff_norm, sobolevWeightedCoeff, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1),
    pow_one, zpow_ofNat, mul_assoc] using h

theorem criticalToTorusH1_mem (c : CriticalSobolev 3) :
    Memℓp (sobolevWeightedCoeff 1 (criticalCoeff 3 c)) 2 := by
  apply ((criticalCoeff_mem 3 c).const_smul (2 : ℂ)).mono'
  intro ki
  change ‖sobolevWeightedCoeff 1 (criticalCoeff 3 c) ki‖ ≤
    ‖(2 : ℂ) * criticalWeightedCoeff 3 (criticalCoeff 3 c) ki‖
  simpa only [norm_mul, Complex.norm_ofNat] using criticalToTorusH1_weighted_bound (criticalCoeff 3 c) ki

theorem exists_criticalToTorusH1Value (c : CriticalSobolev 3) :
    ∃ v : TorusSobolev 1, v.val = criticalCoeff 3 c :=
  ⟨⟨criticalCoeff 3 c, criticalToTorusH1_mem c⟩, Eq.refl (criticalCoeff 3 c)⟩

def criticalToTorusH1Value (c : CriticalSobolev 3) : TorusSobolev 1 :=
  (exists_criticalToTorusH1Value c).choose

@[simp]
theorem criticalToTorusH1Value_coeff (c : CriticalSobolev 3) :
    (criticalToTorusH1Value c).val = criticalCoeff 3 c :=
  (exists_criticalToTorusH1Value c).choose_spec

def criticalToTorusH1Linear : CriticalSobolev 3 →ₗ[ℂ] TorusSobolev 1 where
  toFun := criticalToTorusH1Value
  map_add' c d := by
    apply Subtype.ext
    change (criticalToTorusH1Value (c + d)).val =
      (criticalToTorusH1Value c).val + (criticalToTorusH1Value d).val
    rw [criticalToTorusH1Value_coeff, criticalToTorusH1Value_coeff,
      criticalToTorusH1Value_coeff, criticalCoeff_add]
  map_smul' z c := by
    apply Subtype.ext
    change (criticalToTorusH1Value (z • c)).val = z • (criticalToTorusH1Value c).val
    rw [criticalToTorusH1Value_coeff, criticalToTorusH1Value_coeff, criticalCoeff_smul]

@[simp]
theorem criticalToTorusH1Linear_coeff (c : CriticalSobolev 3) :
    (criticalToTorusH1Linear c).val = criticalCoeff 3 c := criticalToTorusH1Value_coeff c

theorem criticalToTorusH1Linear_norm_le (c : CriticalSobolev 3) :
    ‖criticalToTorusH1Linear c‖ ≤ 2 * ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr 1 (criticalToTorusH1Linear c)‖ :=
      ((torusSobolevRepr 1).norm_map _).symm
    _ ≤ ‖(2 : ℂ) • criticalSobolevRepr 3 c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      simp only [torusSobolevRepr_apply, criticalToTorusH1Linear_coeff]
      change ‖sobolevWeightedCoeff 1 (criticalCoeff 3 c) ki‖ ≤
        ‖(2 : ℂ) * criticalWeightedCoeff 3 (criticalCoeff 3 c) ki‖
      simpa only [norm_mul, Complex.norm_ofNat] using criticalToTorusH1_weighted_bound (criticalCoeff 3 c) ki
    _ = _ := by rw [norm_smul, Complex.norm_ofNat, (criticalSobolevRepr 3).norm_map]

/-- The actual H^(3/2) coefficient array as an H¹ vector. -/
def criticalToTorusH1 : CriticalSobolev 3 →L[ℂ] TorusSobolev 1 :=
  criticalToTorusH1Linear.mkContinuous 2 criticalToTorusH1Linear_norm_le

@[simp]
theorem criticalToTorusH1_coeff (c : CriticalSobolev 3) :
    (criticalToTorusH1 c).val = criticalCoeff 3 c := by
  unfold criticalToTorusH1
  exact (congrArg (fun v : TorusSobolev 1 => v.val)
    (criticalToTorusH1Linear.mkContinuous_apply 2 criticalToTorusH1Linear_norm_le c)).trans
    (criticalToTorusH1Linear_coeff c)

theorem criticalToTorusH1_norm_le (c : CriticalSobolev 3) :
    ‖criticalToTorusH1 c‖ ≤ 2 * ‖c‖ := criticalToTorusH1Linear_norm_le c

/-- Actual physical torus L² realization; its Fourier coefficients are the input array. -/
def criticalPhysicalL2 (q : ℤ) (hq : 0 ≤ q) : CriticalSobolev q →L[ℂ] TorusVectorL2 :=
  torusSobolevL2.toContinuousLinearMap.comp (criticalToTorusH0 q hq)

theorem criticalPhysicalL2_fourierCoeff (q : ℤ) (hq : 0 ≤ q) (c : CriticalSobolev q) :
    torusVectorFourierCoeff (criticalPhysicalL2 q hq c) = criticalCoeff q c := by
  change torusVectorFourierCoeff (torusSobolevL2 (criticalToTorusH0 q hq c)) = _
  rw [torusSobolevL2_fourierCoeff, criticalToTorusH0_coeff]

theorem criticalPhysicalL2_norm_le (q : ℤ) (hq : 0 ≤ q) (c : CriticalSobolev q) :
    ‖criticalPhysicalL2 q hq c‖ ≤ ‖c‖ := by
  change ‖torusSobolevL2 (criticalToTorusH0 q hq c)‖ ≤ _
  rw [torusSobolevL2_norm]
  exact criticalToTorusH0_norm_le q hq c

end

end SingularClosure
