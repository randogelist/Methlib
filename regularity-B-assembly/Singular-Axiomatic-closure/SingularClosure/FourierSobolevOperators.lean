import SingularClosure.TorusGalerkinSobolev
import SingularClosure.LerayL2Contraction

/-! Concrete continuous linear operations on the weighted Fourier Sobolev spaces. -/

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal

namespace SingularClosure

noncomputable section

theorem torusSobolev_weightedCoeff_norm (s : ℕ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s c ki‖ =
      torusSobolevWeight ki.1 ^ s * ‖c ki.1 ki.2‖ := by
  simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1)]

theorem torusSobolev_weightedCoeff_norm_mono {s t : ℕ} (hst : s ≤ t)
    (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s c ki‖ ≤ ‖sobolevWeightedCoeff t c ki‖ := by
  rw [torusSobolev_weightedCoeff_norm, torusSobolev_weightedCoeff_norm]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (torusSobolevWeight_one_le ki.1) hst) (norm_nonneg _)

def torusSobolevLowerLinear (s t : ℕ) (hst : s ≤ t) :
    TorusSobolev t →ₗ[ℂ] TorusSobolev s where
  toFun c := ⟨c.val, c.property.mono' (torusSobolev_weightedCoeff_norm_mono hst c.val)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in
theorem torusSobolevLowerLinear_norm_le (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    ‖torusSobolevLowerLinear s t hst c‖ ≤ ‖c‖ := by
  change ‖torusSobolevReprLinear s (torusSobolevLowerLinear s t hst c)‖ ≤
    ‖torusSobolevReprLinear t c‖
  exact lp.norm_mono (by norm_num) (torusSobolev_weightedCoeff_norm_mono hst c.val)

def torusSobolevLower (s t : ℕ) (hst : s ≤ t) : TorusSobolev t →L[ℂ] TorusSobolev s :=
  (torusSobolevLowerLinear s t hst).mkContinuous 1
    (fun c => by simpa using torusSobolevLowerLinear_norm_le s t hst c)

@[simp]
theorem torusSobolevLower_coeff (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    (torusSobolevLower s t hst c).val = c.val := rfl

theorem torusSobolevLower_coeff_apply (s t : ℕ) (hst : s ≤ t)
    (c : TorusSobolev t) (k : Frequency) (i : Fin 3) :
    (torusSobolevLower s t hst c).val k i = c.val k i := rfl

theorem torusSobolevLower_norm_le (s t : ℕ) (hst : s ≤ t) (c : TorusSobolev t) :
    ‖torusSobolevLower s t hst c‖ ≤ ‖c‖ :=
  torusSobolevLowerLinear_norm_le s t hst c

theorem torusSobolev_finite_weighted_sum_le (s : ℕ) (c : TorusSobolev s)
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖sobolevWeightedCoeff s c.val ki‖ ^ 2) ≤ ‖c‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
    (torusSobolevRepr s c) S
  simpa only [ENNReal.toReal_ofNat, Real.rpow_natCast,
    torusSobolevRepr_apply, sobolevWeightedCoeff, (torusSobolevRepr s).norm_map] using h

theorem torusSobolev_multiplier_weighted_norm_le (s t : ℕ)
    (b : Frequency → ℂ) (B : ℝ)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff s (fun k i => b k * c k i) ki‖ ≤
      B * ‖sobolevWeightedCoeff t c ki‖ := by
  rw [torusSobolev_weightedCoeff_norm, torusSobolev_weightedCoeff_norm, norm_mul]
  calc
    _ = (torusSobolevWeight ki.1 ^ s * ‖b ki.1‖) * ‖c ki.1 ki.2‖ := by ring
    _ ≤ (B * torusSobolevWeight ki.1 ^ t) * ‖c ki.1 ki.2‖ :=
      mul_le_mul_of_nonneg_right (hb ki.1) (norm_nonneg _)
    _ = _ := by ring

def torusSobolevMultiplierLinear (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t) :
    TorusSobolev t →ₗ[ℂ] TorusSobolev s where
  toFun c := ⟨fun k i => b k * c.val k i, by
    apply (c.property.const_smul (B : ℂ)).mono'
    intro ki
    change ‖sobolevWeightedCoeff s (fun k i => b k * c.val k i) ki‖ ≤
      ‖(B : ℂ) * sobolevWeightedCoeff t c.val ki‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
    exact torusSobolev_multiplier_weighted_norm_le s t b B hb c.val ki⟩
  map_add' c d := by
    apply Subtype.ext
    funext k i
    exact mul_add _ _ _
  map_smul' z c := by
    apply Subtype.ext
    funext k i
    exact mul_left_comm _ _ _

set_option maxHeartbeats 1000000 in
theorem torusSobolevMultiplierLinear_norm_le (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    ‖torusSobolevMultiplierLinear s t b B hB hb c‖ ≤ B * ‖c‖ := by
  change ‖torusSobolevReprLinear s (torusSobolevMultiplierLinear s t b B hB hb c)‖ ≤ B * ‖c‖
  calc
    _ ≤ ‖(B : ℂ) • torusSobolevRepr t c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      change ‖sobolevWeightedCoeff s (fun k i => b k * c.val k i) ki‖ ≤
        ‖(B : ℂ) * sobolevWeightedCoeff t c.val ki‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
      exact torusSobolev_multiplier_weighted_norm_le s t b B hb c.val ki
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB,
        (torusSobolevRepr t).norm_map]

def torusSobolevMultiplier (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t) :
    TorusSobolev t →L[ℂ] TorusSobolev s :=
  (torusSobolevMultiplierLinear s t b B hB hb).mkContinuous B
    (torusSobolevMultiplierLinear_norm_le s t b B hB hb)

@[simp]
theorem torusSobolevMultiplier_coeff (s t : ℕ) (b : Frequency → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k, torusSobolevWeight k ^ s * ‖b k‖ ≤ B * torusSobolevWeight k ^ t)
    (c : TorusSobolev t) :
    (torusSobolevMultiplier s t b B hB hb c).val = fun k i => b k * c.val k i := rfl

theorem torusSobolev_laplacian_multiplier_bound (s : ℕ) (k : Frequency) :
    torusSobolevWeight k ^ s * ‖-(laplacianFrequency k : ℂ)‖ ≤
      1 * torusSobolevWeight k ^ (s + 2) := by
  have hfreq : 0 ≤ laplacianFrequency k := by
    unfold laplacianFrequency
    have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
      exact_mod_cast galerkinFreqSq_nonneg k
    positivity
  have hweight : laplacianFrequency k ≤ torusSobolevWeight k ^ 2 := by
    rw [torusSobolevWeight_sq]
    unfold laplacianFrequency
    linarith
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfreq,
    one_mul, pow_add]
  exact mul_le_mul_of_nonneg_left hweight (pow_nonneg (torusSobolevWeight_pos k).le s)

def torusSobolevLaplacian (s : ℕ) : TorusSobolev (s + 2) →L[ℂ] TorusSobolev s :=
  torusSobolevMultiplier s (s + 2) (fun k => -(laplacianFrequency k : ℂ))
    1 zero_le_one (torusSobolev_laplacian_multiplier_bound s)

@[simp]
theorem torusSobolevLaplacian_coeff (s : ℕ) (c : TorusSobolev (s + 2)) :
    (torusSobolevLaplacian s c).val = fun k i => -(laplacianFrequency k : ℂ) * c.val k i := rfl

def torusSobolevViscous (ν : ℝ) (s : ℕ) : TorusSobolev (s + 2) →L[ℂ] TorusSobolev s :=
  (ν : ℂ) • torusSobolevLaplacian s

@[simp]
theorem torusSobolevViscous_coeff (ν : ℝ) (s : ℕ) (c : TorusSobolev (s + 2)) :
    (torusSobolevViscous ν s c).val = fun k i =>
      -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i := by
  funext k i
  change (ν : ℂ) * (-(laplacianFrequency k : ℂ) * c.val k i) = _
  simp only [laplacianFrequency, Complex.ofReal_mul]
  ring

theorem coefficientLeray_add_arg (k : Frequency) (v w : Fin 3 → ℂ) :
    coefficientLeray k (v + w) = coefficientLeray k v + coefficientLeray k w := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, if_neg hk, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, add_div]
    ring

theorem coefficientLeray_smul_arg (k : Frequency) (z : ℂ) (v : Fin 3 → ℂ) :
    coefficientLeray k (z • v) = z • coefficientLeray k v := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · have hsum : (∑ j : Fin 3, (k j : ℂ) * (z * v j)) =
        z * ∑ j : Fin 3, (k j : ℂ) * v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [coefficientLeray, if_neg hk, Pi.smul_apply, smul_eq_mul, hsum]
    ring

theorem torusSobolev_leray_mode_sum_le (s : ℕ) (c : FourierCoeff) (k : Frequency) :
    (∑ i : Fin 3, ‖sobolevWeightedCoeff s (lerayFourierCoeff c) (k, i)‖ ^ 2) ≤
      ∑ i : Fin 3, ‖sobolevWeightedCoeff s c (k, i)‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (coefficientLeray_energy_le k (c k))
    (sq_nonneg (torusSobolevWeight k ^ s))
  simpa only [torusSobolev_weightedCoeff_norm, lerayFourierCoeff,
    Complex.normSq_eq_norm_sq, Finset.mul_sum, mul_pow] using h

theorem torusSobolev_leray_finite_sum_le (s : ℕ) (c : TorusSobolev s)
    (S : Finset FourierIndex) :
    (∑ ki ∈ S, ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^ 2) ≤ ‖c‖ ^ 2 := by
  classical
  have hsub : S ⊆ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => sq_nonneg _)
    _ = ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) (k, i)‖ ^ 2 := by
      rw [Finset.sum_product]
    _ ≤ ∑ k ∈ S.image Prod.fst, ∑ i : Fin 3,
        ‖sobolevWeightedCoeff s c.val (k, i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k hk => torusSobolev_leray_mode_sum_le s c.val k)
    _ = ∑ ki ∈ (S.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff s c.val ki‖ ^ 2 := by rw [Finset.sum_product]
    _ ≤ ‖c‖ ^ 2 := torusSobolev_finite_weighted_sum_le s c _

def torusSobolevLerayLinear (s : ℕ) : TorusSobolev s →ₗ[ℂ] TorusSobolev s where
  toFun c := ⟨lerayFourierCoeff c.val, by
    apply memℓp_gen' (C := ‖c‖ ^ 2)
    intro S
    simpa only [ENNReal.toReal_ofNat, Real.rpow_natCast] using
      torusSobolev_leray_finite_sum_le s c S⟩
  map_add' c d := by
    apply Subtype.ext
    funext k
    exact coefficientLeray_add_arg k (c.val k) (d.val k)
  map_smul' z c := by
    apply Subtype.ext
    funext k
    exact coefficientLeray_smul_arg k z (c.val k)

set_option maxHeartbeats 1000000 in
theorem torusSobolevLerayLinear_norm_le (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLerayLinear s c‖ ≤ ‖c‖ := by
  change ‖torusSobolevReprLinear s (torusSobolevLerayLinear s c)‖ ≤ ‖c‖
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg c)
  intro S
  change (∑ ki ∈ S, ‖sobolevWeightedCoeff s (lerayFourierCoeff c.val) ki‖ ^
    (2 : ℝ≥0∞).toReal) ≤ ‖c‖ ^ (2 : ℝ≥0∞).toReal
  simpa only [ENNReal.toReal_ofNat, Real.rpow_natCast] using
    torusSobolev_leray_finite_sum_le s c S

def torusSobolevLeray (s : ℕ) : TorusSobolev s →L[ℂ] TorusSobolev s :=
  (torusSobolevLerayLinear s).mkContinuous 1
    (fun c => by simpa using torusSobolevLerayLinear_norm_le s c)

@[simp]
theorem torusSobolevLeray_coeff (s : ℕ) (c : TorusSobolev s) :
    (torusSobolevLeray s c).val = lerayFourierCoeff c.val := rfl

theorem torusSobolevLeray_norm_le (s : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevLeray s c‖ ≤ ‖c‖ := torusSobolevLerayLinear_norm_le s c

end

end SingularClosure
