import QuasiFeffermanB.EnergyTestDecay
import SingularClosure.PeriodicFourierInjective
import SingularClosure.SobolevSmoothRealization
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform convergence of the actual differentiated test projections

Status: A_TIER_CANDIDATE.  External elaboration and theorem-level axiom audits
are pending; the cached baseline run does not certify these declarations.

QFB: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c.
Foundation: 09dfe94a1ef150e21d09df3013fbe09002ef139c.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

The Galerkin cutoff omits the zero mode.  Its derivative is zero, so the
derivative limit is the original derivative even for tests with nonzero mean.
The all-cutoff operator bound and uniform convergence use the same proved
summable Fourier majorant on the entire positive compact time slab.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal ContDiff

namespace QuasiFeffermanB

open SingularClosure

noncomputable section

/-- The existing zero-completed Euclidean frequency cutoff is cofinal among
finite frequency sets. -/
theorem energy_sobolevCutoffModes_tendsto :
    Tendsto sobolevCutoffModes atTop atTop := by
  classical
  have hmem (k : Frequency) : ∀ᶠ N : ℕ in atTop, k ∈ sobolevCutoffModes N := by
    by_cases hk : k = 0
    · subst k
      exact Filter.Eventually.of_forall (fun N => by simp [sobolevCutoffModes])
    · obtain ⟨M, hM⟩ := exists_nat_gt (galerkinFreqSq k)
      filter_upwards [eventually_ge_atTop (M + 1)] with N hN
      apply Finset.mem_insert_of_mem
      apply mem_cutoffModes_of_freqSq_le hk
      have hMN : (M : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast (Nat.le_trans (Nat.le_succ M) hN)
      have h1N : (1 : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le M)) hN)
      nlinarith [sq_nonneg ((N : ℤ) - 1)]
  apply tendsto_atTop.2
  intro K
  induction K using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (fun N => Finset.empty_subset _)
  | @insert k K hk ih =>
      filter_upwards [hmem k, ih] with N hkN hKN
      change insert k K ⊆ sobolevCutoffModes N
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hkN
      · exact hKN hl

/-- Reconstruction from the literal cube Fourier integrals of a smooth
periodic field.  The zero coefficient is retained by this full series. -/
theorem energy_smooth_datumFourier_reconstruction
    (f : Field) (hf : ContDiff ℝ ∞ f) (hfp : SpatialPeriodic f) :
    f = smoothFourierSynthesis (datumFourierCoeff f) := by
  have hrapid : ∀ i : Fin 3, RapidScalarFourier (fun k => datumFourierCoeff f k i) :=
    ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff f)
      (fun m => SMOOTH_DATUM_MEM_TORUS_SOBOLEV m f hf hfp)
  apply datumFourierCoeff_injective_continuous_periodic f
    (smoothFourierSynthesis (datumFourierCoeff f)) hf.continuous
    (smoothFourierSynthesis_contDiff (datumFourierCoeff f) hrapid).continuous
    hfp (smoothFourierSynthesis_periodic (datumFourierCoeff f))
  exact (datumFourierCoeff_smoothFourierSynthesis (datumFourierCoeff f) hrapid
    (datumFourierCoeff_reality f)).symm

/-- Every matrix entry of the actual derivative equals its differentiated
Fourier series, pointwise on the physical lift. -/
theorem energy_smooth_derivative_fourierSeries
    (f : Field) (hf : ContDiff ℝ ∞ f) (hfp : SpatialPeriodic f)
    (j i : Fin 3) (x : Vec) :
    (fderiv ℝ f x (unitVector j)) i =
      (∑' k : Frequency, fourierCharacter k x *
        (derivativeSymbol j k * datumFourierCoeff f k i)).re := by
  have hrapid : ∀ l : Fin 3, RapidScalarFourier (fun k => datumFourierCoeff f k l) :=
    ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff f)
      (fun m => SMOOTH_DATUM_MEM_TORUS_SOBOLEV m f hf hfp)
  have hd : coordinateDerivative f j =
      smoothFourierSynthesis (spectralMultiplier (derivativeSymbol j) (datumFourierCoeff f)) := by
    calc
      coordinateDerivative f j =
          coordinateDerivative (smoothFourierSynthesis (datumFourierCoeff f)) j :=
        congrArg (fun h : Field => coordinateDerivative h j)
          (energy_smooth_datumFourier_reconstruction f hf hfp)
      _ = _ := smoothFourierSynthesis_coordinateDerivative (datumFourierCoeff f) hrapid j
  exact congrArg (fun h : Field => h x i) hd

/-- The corresponding finite matrix entry uses exactly the original cutoff. -/
theorem energy_finite_derivative_fourierSum
    (N : ℕ) (c : FourierCoeff) (j i : Fin 3) (x : Vec) :
    (fderiv ℝ (finiteSynthesis N c) x (unitVector j)) i =
      (∑ k ∈ cutoffModes N,
        fourierCharacter k x * (derivativeSymbol j k * c k i)).re := by
  exact congrArg (fun h : Field => h x i) (finiteSynthesis_coordinateDerivative N c j)

private theorem energy_sum_coordinates (v : Vec) :
    (∑ i : Fin 3, v i • unitVector i) = v := by
  ext j
  simp [unitVector, Pi.single_apply, mul_ite]

/-- A dimension-explicit norm bound from the three real coordinates. -/
theorem energy_vector_norm_le_three
    (v : Vec) (b : ℝ) (hb : ∀ i : Fin 3, |v i| ≤ b) :
    ‖v‖ ≤ 3 * b := by
  calc
    ‖v‖ = ‖∑ i : Fin 3, v i • unitVector i‖ := by rw [energy_sum_coordinates]
    _ ≤ ∑ i : Fin 3, ‖v i • unitVector i‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, |v i| := by simp [norm_smul, unitVector, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin 3, b := Finset.sum_le_sum (fun i _ => hb i)
    _ = 3 * b := by simp

/-- Nine entry bounds control the actual Euclidean operator norm. -/
theorem energy_operator_norm_le_nine
    (A : Vec →L[ℝ] Vec) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ j i : Fin 3, |(A (unitVector j)) i| ≤ b) :
    ‖A‖ ≤ 9 * b := by
  have hcolumn (j : Fin 3) : ‖A (unitVector j)‖ ≤ 3 * b :=
    energy_vector_norm_le_three (A (unitVector j)) b (hA j)
  apply A.opNorm_le_bound (mul_nonneg (by norm_num) hb)
  intro v
  have hexpand : A v = ∑ j : Fin 3, v j • A (unitVector j) := by
    calc
      A v = A (∑ j : Fin 3, v j • unitVector j) := by rw [energy_sum_coordinates]
      _ = _ := by simp only [map_sum, map_smul]
  calc
    ‖A v‖ = ‖∑ j : Fin 3, v j • A (unitVector j)‖ := by rw [hexpand]
    _ ≤ ∑ j : Fin 3, ‖v j • A (unitVector j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, |v j| * ‖A (unitVector j)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _j : Fin 3, ‖v‖ * (3 * b) := by
      apply Finset.sum_le_sum
      intro j _
      have hvj : |v j| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
      exact mul_le_mul hvj (hcolumn j) (norm_nonneg _) (norm_nonneg _)
    _ = (9 * b) * ‖v‖ := by simp <;> ring

/-- One uniform complex-series estimate simultaneously controls all nine
derivative entries and all spacetime points of the slab. -/
theorem energyTest_derivative_entries_uniform
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) :
    TendstoUniformlyOn
      (fun N (z : (Fin 3 × Fin 3) × (ℝ × Vec)) =>
        ∑ k ∈ cutoffModes N, fourierCharacter k z.2.2 *
          (derivativeSymbol z.1.1 k * datumFourierCoeff (φ z.2.1) k z.1.2))
      (fun z : (Fin 3 × Fin 3) × (ℝ × Vec) =>
        ∑' k : Frequency, fourierCharacter k z.2.2 *
          (derivativeSymbol z.1.1 k * datumFourierCoeff (φ z.2.1) k z.1.2))
      atTop (Set.univ ×ˢ ((Icc s t) ×ˢ unitCube)) := by
  classical
  obtain ⟨C, hC, hsum, hbound⟩ :=
    ENERGY_TEST_UNIFORM_DERIVATIVE_MAJORANT φ hφ s t hs
  let F : Frequency → ((Fin 3 × Fin 3) × (ℝ × Vec)) → ℂ :=
    fun k z => fourierCharacter k z.2.2 *
      (derivativeSymbol z.1.1 k * datumFourierCoeff (φ z.2.1) k z.1.2)
  let S : Set ((Fin 3 × Fin 3) × (ℝ × Vec)) :=
    Set.univ ×ˢ ((Icc s t) ×ˢ unitCube)
  have hU : TendstoUniformlyOn
      (fun K : Finset Frequency => fun z => ∑ k ∈ K, F k z)
      (fun z => ∑' k, F k z) atTop S := by
    apply tendstoUniformlyOn_tsum hsum
    intro k z hz
    change ‖fourierCharacter k z.2.2 *
      (derivativeSymbol z.1.1 k * datumFourierCoeff (φ z.2.1) k z.1.2)‖ ≤ _
    rw [norm_mul, fourierCharacter_norm, one_mul]
    exact hbound z.2.1 hz.2.1 z.1.1 k z.1.2
  have hV : TendstoUniformlyOn
      (fun N : ℕ => fun z => ∑ k ∈ sobolevCutoffModes N, F k z)
      (fun z => ∑' k, F k z) atTop S := by
    intro v hv
    exact energy_sobolevCutoffModes_tendsto.eventually (hU v hv)
  apply hV.congr
  apply Filter.Eventually.of_forall
  intro N z hz
  change (∑ k ∈ insert (0 : Frequency) (cutoffModes N), F k z) = _
  rw [Finset.sum_insert (cutoffModes_zero_not_mem N)]
  have hzero : F 0 z = 0 := by simp [F, derivativeSymbol]
  rw [hzero, zero_add]
  rfl

/-- Uniform convergence in the actual spatial operator norm of the original
Galerkin test projections, for every positive compact time slab. -/
theorem ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    TendstoUniformlyOn
      (fun N (z : ℝ × Vec) =>
        fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ z.1))) z.2)
      (fun z : ℝ × Vec => fderiv ℝ (φ z.1) z.2)
      atTop ((Icc s t) ×ˢ unitCube) := by
  have hU := energyTest_derivative_entries_uniform φ hφ s t hs
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hε18 : 0 < ε / 18 := by positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (ε / 18) hε18] with N hN
  intro z hz
  have ht : 0 < z.1 := hs.trans_le hz.1.1
  have hentry : ∀ j i : Fin 3,
      |((fderiv ℝ (φ z.1) z.2 -
          fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ z.1))) z.2)
          (unitVector j)) i| ≤ ε / 18 := by
    intro j i
    have hdist := hN ((j, i), z) ⟨Set.mem_univ _, hz⟩
    rw [dist_eq_norm] at hdist
    change |(fderiv ℝ (φ z.1) z.2 (unitVector j)) i -
      (fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ z.1))) z.2
        (unitVector j)) i| ≤ ε / 18
    rw [energy_smooth_derivative_fourierSeries (φ z.1)
      (hφ.spatial_smooth ht) (hφ.periodic z.1 ht) j i z.2,
      energy_finite_derivative_fourierSum N (datumFourierCoeff (φ z.1)) j i z.2]
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hdist.le
  calc
    dist (fderiv ℝ (φ z.1) z.2)
        (fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ z.1))) z.2) =
      ‖fderiv ℝ (φ z.1) z.2 -
        fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ z.1))) z.2‖ := dist_eq_norm _ _
    _ ≤ 9 * (ε / 18) := energy_operator_norm_le_nine _ _ hε18.le hentry
    _ < ε := by linarith

/-- A fixed operator bound holds for every cutoff, including all initial
cutoffs; it can be used directly as a domination constant. -/
theorem ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND
    (φ : Velocity) (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N r, r ∈ Icc s t → ∀ x ∈ unitCube,
      ‖fderiv ℝ (finiteSynthesis N (datumFourierCoeff (φ r))) x‖ ≤ C := by
  obtain ⟨C, hC, hsum, hbound⟩ :=
    ENERGY_TEST_UNIFORM_DERIVATIVE_MAJORANT φ hφ s t hs
  have hnonneg (k : Frequency) : 0 ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
    positivity
  have htotal : 0 ≤ ∑' k : Frequency, C * (torusSobolevWeight k)⁻¹ ^ 4 :=
    tsum_nonneg hnonneg
  refine ⟨9 * ∑' k : Frequency, C * (torusSobolevWeight k)⁻¹ ^ 4,
    mul_nonneg (by norm_num) htotal, ?_⟩
  intro N r hr x hx
  apply energy_operator_norm_le_nine _ _ htotal
  intro j i
  rw [energy_finite_derivative_fourierSum]
  calc
    |(∑ k ∈ cutoffModes N,
        fourierCharacter k x * (derivativeSymbol j k * datumFourierCoeff (φ r) k i)).re| ≤
      ‖∑ k ∈ cutoffModes N,
        fourierCharacter k x * (derivativeSymbol j k * datumFourierCoeff (φ r) k i)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ cutoffModes N,
        ‖fourierCharacter k x * (derivativeSymbol j k * datumFourierCoeff (φ r) k i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ cutoffModes N, C * (torusSobolevWeight k)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, fourierCharacter_norm, one_mul]
      exact hbound r hr j k i
    _ ≤ ∑' k : Frequency, C * (torusSobolevWeight k)⁻¹ ^ 4 :=
      hsum.sum_le_tsum (cutoffModes N) (fun k _ => hnonneg k)

end

end QuasiFeffermanB
