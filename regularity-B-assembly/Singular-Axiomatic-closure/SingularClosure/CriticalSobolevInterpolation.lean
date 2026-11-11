import SingularClosure.CriticalSobolevDual

/-! The actual analytic-family L2/L6 interpolation estimate.  The proof uses
the concrete regularized dual function, differentiation under the cube
integral, Hölder at both strip boundaries, and Hadamard's theorem. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SingularClosure

noncomputable section

theorem critical_sqrt_mass_product {A B J : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J) :
    Real.sqrt (A * J ^ (1 / 2 : ℝ)) * Real.sqrt (B * J ^ (5 / 6 : ℝ)) =
      (Real.sqrt A * Real.sqrt B) * J ^ (2 / 3 : ℝ) := by
  rw [Real.sqrt_mul hA, Real.sqrt_mul hB]
  have hhalf : Real.sqrt (J ^ (1 / 2 : ℝ)) = J ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hJ]
    norm_num
  have hfive : Real.sqrt (J ^ (5 / 6 : ℝ)) = J ^ (5 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hJ]
    norm_num
  rw [hhalf, hfive]
  calc
    _ = (Real.sqrt A * Real.sqrt B) * (J ^ (1 / 4 : ℝ) * J ^ (5 / 12 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hJ (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (0 : ℝ) ≤ 5 / 12)]
      norm_num

/-- The midpoint pairing is at least the literal cubic norm integral. -/
theorem critical_midpoint_pairing_lower (u : Vec → ℂ) (hu : Continuous u)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in unitCube, ‖u x‖ ^ 3) ≤
      ‖∫ x in unitCube, u x * criticalDualFamily u δ (1 / 2) x‖ := by
  have hpoint (x : Vec) : u x * criticalDualFamily u δ (1 / 2) x =
      ((‖u x‖ ^ 2 * criticalDualBase u δ x : ℝ) : ℂ) := by
    rw [criticalDualFamily_midpoint u hδ x, ← mul_assoc]
    simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_mul]
  have hint : (∫ x in unitCube, u x * criticalDualFamily u δ (1 / 2) x) =
      ((∫ x in unitCube, ‖u x‖ ^ 2 * criticalDualBase u δ x : ℝ) : ℂ) := by
    simp_rw [hpoint]
    exact integral_complex_ofReal
  have hn : 0 ≤ ∫ x in unitCube, ‖u x‖ ^ 2 * criticalDualBase u δ x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (criticalDualBase_pos u hδ x).le)
  rw [hint, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  apply integral_mono
    ((hu.norm.pow 3).continuousOn.integrableOn_compact isCompact_unitCube)
    (((hu.norm.pow 2).mul (criticalDualBase_continuous u hu δ)).continuousOn.integrableOn_compact
      isCompact_unitCube)
  intro x
  dsimp [criticalDualBase]
  nlinarith [sq_nonneg ‖u x‖]

/-- A proved interpolation step for a genuinely holomorphic scalar field
family.  Endpoint bounds and derivatives are explicit data; this theorem
does not assert any fractional Fourier embedding by itself. -/
theorem critical_analytic_family_regularized_bound
    (F D : ℂ → Vec → ℂ)
    (hF : Continuous (fun q : ℂ × Vec => F q.1 q.2))
    (hD : Continuous (fun q : ℂ × Vec => D q.1 q.2))
    (hd : ∀ z x, HasDerivAt (fun w => F w x) (D z x) z)
    (hstrip : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ∀ x ∈ unitCube, ‖F z x‖ ≤ M)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : ∀ z : ℂ, z.re = 0 →
      lpNorm (F z) 2 (volume.restrict unitCube) ≤ A)
    (hright : ∀ z : ℂ, z.re = 1 →
      lpNorm (F z) 6 (volume.restrict unitCube) ≤ B)
    (δ : ℝ) (hδ : 0 < δ) :
    (∫ x in unitCube, ‖F (1 / 2) x‖ ^ 3) ≤
      (Real.sqrt A * Real.sqrt B) * criticalDualMass (F (1 / 2)) δ ^ (2 / 3 : ℝ) := by
  let u : Vec → ℂ := F (1 / 2)
  have hu : Continuous u := hF.comp (continuous_const.prodMk continuous_id)
  let G : ℂ → Vec → ℂ := criticalDualFamily u δ
  let H : ℂ → ℂ := fun z => ∫ x in unitCube, F z x * G z x
  have hG : Continuous (fun q : ℂ × Vec => G q.1 q.2) :=
    criticalDualFamily_continuous u hu hδ
  have hlog : Continuous (fun x => (Real.log (criticalDualBase u δ x) : ℂ)) :=
    Complex.continuous_ofReal.comp ((criticalDualBase_continuous u hu δ).log
      (fun x => (criticalDualBase_pos u hδ x).ne'))
  have hH : Differentiable ℂ H := by
    apply critical_differentiable_cube_integral
      (fun z x => F z x * G z x)
      (fun z x => D z x * G z x +
        F z x * (G z x * (Real.log (criticalDualBase u δ x) : ℂ)))
      (hF.mul hG) ((hD.mul hG).add (hF.mul (hG.mul (hlog.comp continuous_snd))))
    intro z x
    exact (hd z x).mul (criticalDualFamily_hasDerivAt u δ z x)
  obtain ⟨M, hM, hFM⟩ := hstrip
  obtain ⟨L, hL⟩ := isCompact_unitCube.exists_bound_of_continuousOn hlog.continuousOn
  let P : ℝ := M * (M * Real.exp (2 * max L 0))
  have hbounded : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖H z‖ ≤ C := by
    refine ⟨∫ _x in unitCube, P, ?_⟩
    intro z hz0 hz1
    have hp (x : Vec) (hx : x ∈ unitCube) : ‖F z x * G z x‖ ≤ P := by
      have huM : ‖u x‖ ≤ M := hFM (1 / 2) (by norm_num) (by norm_num) x hx
      have hlogL : |Real.log (criticalDualBase u δ x)| ≤ max L 0 := by
        have h := (hL x hx).trans (le_max_left L 0)
        simpa only [Complex.norm_real, Real.norm_eq_abs] using h
      have he : (z.re + 1 / 2) * Real.log (criticalDualBase u δ x) ≤ 2 * max L 0 := by
        calc
          _ ≤ |(z.re + 1 / 2) * Real.log (criticalDualBase u δ x)| := le_abs_self _
          _ = (z.re + 1 / 2) * |Real.log (criticalDualBase u δ x)| := by
            rw [abs_mul, abs_of_nonneg (by linarith)]
          _ ≤ 2 * max L 0 :=
            mul_le_mul (by linarith) hlogL (abs_nonneg _) (by norm_num)
      have hgM : ‖G z x‖ ≤ M * Real.exp (2 * max L 0) := by
        rw [criticalDualFamily_norm u hδ z x,
          Real.rpow_def_of_pos (criticalDualBase_pos u hδ x)]
        apply mul_le_mul huM _ (Real.exp_pos _).le hM
        exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using he)
      rw [norm_mul]
      exact mul_le_mul (hFM z hz0 hz1 x hx) hgM (norm_nonneg _) hM
    calc
      _ ≤ ∫ x in unitCube, ‖F z x * G z x‖ := norm_integral_le_integral_norm _
      _ ≤ _ := integral_mono_ae
        ((((hF.mul hG).comp (continuous_const.prodMk continuous_id)).norm).continuousOn.integrableOn_compact
          isCompact_unitCube)
        (continuous_const.continuousOn.integrableOn_compact isCompact_unitCube)
        (by filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
            exact hp x hx)
  let J : ℝ := criticalDualMass u δ
  have hJ : 0 ≤ J := criticalDualMass_nonneg u hδ.le
  have hHL : ∀ z : ℂ, z.re = 0 → ‖H z‖ ≤ A * J ^ (1 / 2 : ℝ) := by
    intro z hz
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]; norm_num
    have hpair := critical_cube_pairing_bound (F z) (G z)
      (hF.comp (continuous_const.prodMk continuous_id))
      (hG.comp (continuous_const.prodMk continuous_id)) hpq
    norm_num only [ENNReal.ofReal_ofNat] at hpair
    refine hpair.trans (mul_le_mul (hleft z hz) ?_ lpNorm_nonneg hA)
    exact criticalDualFamily_lpNorm_le u hu hδ z 2 (by norm_num)
      (by rw [hz]; norm_num)
  have hHR : ∀ z : ℂ, z.re = 1 → ‖H z‖ ≤ B * J ^ (5 / 6 : ℝ) := by
    intro z hz
    have hpq : (6 : ℝ).HolderConjugate (6 / 5) := by
      rw [Real.holderConjugate_iff]; norm_num
    have hpair := critical_cube_pairing_bound (F z) (G z)
      (hF.comp (continuous_const.prodMk continuous_id))
      (hG.comp (continuous_const.prodMk continuous_id)) hpq
    norm_num only [ENNReal.ofReal_ofNat] at hpair
    refine hpair.trans (mul_le_mul (hright z hz) ?_ lpNorm_nonneg hB)
    have h := criticalDualFamily_lpNorm_le u hu hδ z (6 / 5) (by norm_num)
      (by rw [hz]; norm_num)
    norm_num only [one_div_div] at h
    exact h
  have hmid := critical_three_lines_midpoint H hH hbounded
    (A * J ^ (1 / 2 : ℝ)) (B * J ^ (5 / 6 : ℝ)) hHL hHR
  rw [critical_sqrt_mass_product hA hB hJ] at hmid
  exact (critical_midpoint_pairing_lower u hu hδ).trans hmid

end

end SingularClosure
