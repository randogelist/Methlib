import SingularClosure.CriticalClassicalWeakMomentum
import SingularClosure.SmoothDatumSobolev
import SingularClosure.HighOrderEstimate

/-! Uniform Fourier decay of genuine positive-time smooth test fields on
compact time slabs. Constants are derived from the physical derivatives. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_positive_iteratedDerivative_smooth (φ : Velocity)
    (hφ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => φ z.1 z.2) {z | 0 < z.1})
    (j : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => iteratedCoordinateDerivative j m (φ z.1) z.2)
      {z | 0 < z.1} := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
      exact critical_positive_coordinateDerivative_smooth
        (fun t => iteratedCoordinateDerivative j m (φ t)) ih j

theorem energyTest_fourierDecayConstant_continuousOn
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (m : ℕ) (s t : ℝ) (hs : 0 < s) :
    ContinuousOn (fun r => fourierDecayConstant m (φ r)) (Icc s t) := by
  unfold fourierDecayConstant
  apply continuousOn_finset_sum
  intro i _
  apply ContinuousOn.add
  · apply critical_real_cube_integral_continuousOn_Icc
      (fun r x => ‖φ r x i‖) _ s t hs
    exact ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      hφ.smooth.continuousOn).norm
  · apply continuousOn_finset_sum
    intro j _
    unfold coordinateDerivativeL1
    apply critical_real_cube_integral_continuousOn_Icc
      (fun r x => ‖iteratedCoordinateDerivative j m (φ r) x i‖) _ s t hs
    exact ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      (energy_positive_iteratedDerivative_smooth φ hφ.smooth j m).continuousOn).norm

theorem ENERGY_TEST_UNIFORM_SOBOLEV_DECAY
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (m : ℕ) (s t : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc s t, ∀ k : Frequency, ∀ i : Fin 3,
      torusSobolevWeight k ^ (m + 2) * ‖datumFourierCoeff (φ r) k i‖ ≤ C := by
  have hcont : ContinuousOn (fun r => smoothDatumDecayConstant m (φ r)) (Icc s t) :=
    (energyTest_fourierDecayConstant_continuousOn φ hφ (2 * (m + 2)) s t hs).const_mul _
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr k i
  calc
    _ ≤ smoothDatumDecayConstant m (φ r) :=
      smooth_datum_sobolev_decay m (φ r) (hφ.spatial_smooth (hs.trans_le hr.1))
        (hφ.periodic r (hs.trans_le hr.1)) k i
    _ ≤ ‖smoothDatumDecayConstant m (φ r)‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (smoothDatumDecayConstant m (φ r))
    _ ≤ C := hC r hr
    _ ≤ max C 0 := le_max_left _ _

/-- A single summable lattice majorant controls every derivative Fourier
coefficient on the entire positive compact slab. -/
theorem ENERGY_TEST_UNIFORM_DERIVATIVE_MAJORANT
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      Summable (fun k : Frequency => C * (torusSobolevWeight k)⁻¹ ^ 4) ∧
      ∀ r ∈ Icc s t, ∀ j : Fin 3, ∀ k : Frequency, ∀ i : Fin 3,
        ‖derivativeSymbol j k * datumFourierCoeff (φ r) k i‖ ≤
          C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  obtain ⟨C, hC, hb⟩ := ENERGY_TEST_UNIFORM_SOBOLEV_DECAY φ hφ 3 s t hs
  refine ⟨C, hC, summable_torusSobolevWeight_inv_four.mul_left C, ?_⟩
  intro r hr j k i
  have hw : 0 < torusSobolevWeight k := torusSobolevWeight_pos k
  have hpow : torusSobolevWeight k ^ 4 *
      ‖derivativeSymbol j k * datumFourierCoeff (φ r) k i‖ ≤ C := by
    calc
      _ ≤ torusSobolevWeight k ^ 4 *
          (torusSobolevWeight k * ‖datumFourierCoeff (φ r) k i‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_weight k j) (norm_nonneg _))
          (by positivity)
      _ = torusSobolevWeight k ^ (3 + 2) * ‖datumFourierCoeff (φ r) k i‖ := by ring
      _ ≤ C := hb r hr k i
  have hdiv : ‖derivativeSymbol j k * datumFourierCoeff (φ r) k i‖ ≤
      C / torusSobolevWeight k ^ 4 :=
    (le_div_iff₀ (pow_pos hw 4)).mpr (by simpa only [mul_comm] using hpow)
  simpa only [div_eq_mul_inv, inv_pow] using hdiv

end
end QuasiFeffermanB
