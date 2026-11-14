import SingularClosure.H12Frontier.Contracts

/-! Explicit product of proved physical Sobolev bounds. The product is kept
separate from the literature-normalized coefficient until that bridge is proved. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace SingularClosure.H12Frontier
noncomputable section

def sixSource : ℝ≥0∞ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY.choose
def derivativeSource : ℝ≥0∞ := FINITE_CRITICAL_DERIVATIVE_L3.choose
def halfSource : ℝ≥0∞ := FINITE_CRITICAL_HHALF_L3.choose

theorem sixSource_finite : sixSource < ⊤ :=
  FINITE_PHYSICAL_L6_FROM_ENSTROPHY.choose_spec.1

theorem derivativeSource_finite : derivativeSource < ⊤ :=
  FINITE_CRITICAL_DERIVATIVE_L3.choose_spec.1

theorem halfSource_finite : halfSource < ⊤ :=
  FINITE_CRITICAL_HHALF_L3.choose_spec.1

def nativeSix : ℝ := sixSource.toReal + 1
def nativeThree : ℝ := derivativeSource.toReal + halfSource.toReal + 1

theorem nativeSix_pos : 0 < nativeSix := by
  unfold nativeSix
  positivity

theorem nativeThree_pos : 0 < nativeThree := by
  unfold nativeThree
  positivity

theorem nativeSix_bound (N : ℕ) (c : FourierCoeff) (hr : SpectralReality c) :
    eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) ≤
      ENNReal.ofReal nativeSix *
        (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
  have hs : sixSource ≤ ENNReal.ofReal nativeSix := by
    rw [← ENNReal.ofReal_toReal sixSource_finite.ne]
    apply ENNReal.ofReal_le_ofReal
    unfold nativeSix
    linarith
  exact (FINITE_PHYSICAL_L6_FROM_ENSTROPHY.choose_spec.2 N c hr).trans
    (mul_le_mul_of_nonneg_right hs bot_le)

theorem nativeThree_bound (N : ℕ) (c : FourierCoeff) :
    eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube) ≤
      ENNReal.ofReal nativeThree *
        (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) := by
  have hs : derivativeSource ≤ ENNReal.ofReal nativeThree := by
    rw [← ENNReal.ofReal_toReal derivativeSource_finite.ne]
    apply ENNReal.ofReal_le_ofReal
    unfold nativeThree
    have hn : 0 ≤ halfSource.toReal := ENNReal.toReal_nonneg
    linarith
  exact (FINITE_CRITICAL_DERIVATIVE_L3.choose_spec.2 N c).trans
    (mul_le_mul_of_nonneg_right hs bot_le)

theorem nativeHalf_bound (N : ℕ) (c : FourierCoeff) :
    eLpNorm (finiteSynthesis N c) 3 (volume.restrict unitCube) ≤
      ENNReal.ofReal nativeThree *
        (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) := by
  have hs : halfSource ≤ ENNReal.ofReal nativeThree := by
    rw [← ENNReal.ofReal_toReal halfSource_finite.ne]
    apply ENNReal.ofReal_le_ofReal
    unfold nativeThree
    have hn : 0 ≤ derivativeSource.toReal := ENNReal.toReal_nonneg
    linarith
  exact (FINITE_CRITICAL_HHALF_L3.choose_spec.2 N c).trans
    (mul_le_mul_of_nonneg_right hs bot_le)

def nativeProduct : ℝ := nativeSix * nativeThree

theorem nativeProduct_pos : 0 < nativeProduct :=
  mul_pos nativeSix_pos nativeThree_pos

theorem EXPLICIT_PRODUCT_NONLINEAR_BOUND
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    |criticalNonlinearPower 1 N c| ≤
      nativeProduct * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c := by
  let A : ℝ≥0∞ := ENNReal.ofReal nativeSix
  let B : ℝ≥0∞ := ENNReal.ofReal nativeThree
  let K : ℝ≥0∞ := A * B
  have hK : K < ⊤ := by dsimp [K, A, B]; finiteness
  have hKr : K.toReal = nativeProduct := by
    dsimp [K, A, B, nativeProduct]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal nativeSix_pos.le,
      ENNReal.toReal_ofReal nativeThree_pos.le]
  have hE2 := criticalEnergy_nonneg 2 N c
  have hE3 := criticalEnergy_nonneg 3 N c
  have hV6 : eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) ≤
      A * (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) := by
    rw [criticalEnergy_two_eq_coefficientDissipation]
    exact nativeSix_bound N c hreal
  have hD3 : eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3
      (volume.restrict unitCube) ≤ B *
        (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) :=
    nativeThree_bound N c
  have hbound : ENNReal.ofReal (abs (criticalNonlinearPower 1 N c)) ≤
      K * ENNReal.ofReal (criticalEnergy 2 N c) *
        (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) *
          eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube)) *
          (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) :=
        criticalNonlinearPower_one_enorm_le N c hsupp hreal hsol
      _ ≤ ((A * (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ)) *
          (B * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ))) *
          (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hV6 hD3 bot_le bot_le) bot_le
      _ = _ := ennreal_critical_holder_product A B _ _
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hE2,
    ENNReal.toReal_ofReal hE3, ← Real.sqrt_eq_rpow] at hr
  have hproduct : criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c) ≤
      Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c := by
    calc
      _ ≤ (Real.sqrt (criticalEnergy 1 N c) * Real.sqrt (criticalEnergy 3 N c)) *
          Real.sqrt (criticalEnergy 3 N c) :=
        mul_le_mul_of_nonneg_right (criticalEnergy_interpolation_sqrt N c)
          (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hE3]
  calc
    _ ≤ K.toReal * criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c) := hr
    _ = K.toReal * (criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c)) := by ring
    _ ≤ K.toReal * (Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c) :=
      mul_le_mul_of_nonneg_left hproduct ENNReal.toReal_nonneg
    _ = _ := by rw [hKr]; ring

def nativeProductCertificate : NonlinearCertificate where
  constant := nativeProduct
  positive := nativeProduct_pos
  bound := EXPLICIT_PRODUCT_NONLINEAR_BOUND

end
end SingularClosure.H12Frontier
