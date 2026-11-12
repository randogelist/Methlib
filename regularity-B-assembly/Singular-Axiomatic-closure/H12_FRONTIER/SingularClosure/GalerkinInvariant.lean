import SingularClosure.GalerkinReality
import SingularClosure.LerayPressure
import SingularClosure.DissipativeODE

/-!
# The actual invariant finite Fourier state space

The state space is the real submodule of finite complex coefficient arrays
satisfying conjugate symmetry and zero Fourier divergence.  Its vector field
is the concrete Fourier--Galerkin Navier--Stokes polynomial.
-/

set_option autoImplicit false

open Set
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem cutoffCoeff_preserves_reality (N : ℕ) {c : FourierCoeff}
    (hc : SpectralReality c) : SpectralReality (cutoffCoeff N c) := by
  intro k i
  by_cases hk : k ∈ cutoffModes N
  · simp [cutoffCoeff, hk, cutoffModes_neg_mem hk, hc k i]
  · have hnk : -k ∉ cutoffModes N := by
      intro h
      exact hk (by simpa using cutoffModes_neg_mem h)
    simp [cutoffCoeff, hk, hnk]

theorem cutoffCoeff_preserves_solenoidal (N : ℕ) {c : FourierCoeff}
    (hc : SpectralSolenoidal c) : SpectralSolenoidal (cutoffCoeff N c) := by
  intro k
  by_cases hk : k ∈ cutoffModes N
  · simpa [cutoffCoeff, hk] using hc k
  · simp [cutoffCoeff, hk]

/-- The complex Hilbert space of the actual cutoff coefficients. -/
abbrev GalerkinHilbertState (N : ℕ) :=
  EuclideanSpace ℂ (↥(cutoffModes N) × Fin 3)

/-- Zero extension of a Hilbert coefficient array. -/
def hilbertCoeff (N : ℕ) (z : GalerkinHilbertState N) : FourierCoeff :=
  extendFiniteState N (fun k i => z (k, i))

theorem hilbertCoeff_add (N : ℕ) (z w : GalerkinHilbertState N) :
    hilbertCoeff N (z + w) = hilbertCoeff N z + hilbertCoeff N w := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;> simp [hilbertCoeff, extendFiniteState, hk]

theorem hilbertCoeff_smul (N : ℕ) (r : ℝ) (z : GalerkinHilbertState N) :
    hilbertCoeff N (r • z) = r • hilbertCoeff N z := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;> simp [hilbertCoeff, extendFiniteState, hk]

theorem hilbertCoeff_zero (N : ℕ) :
    hilbertCoeff N (0 : GalerkinHilbertState N) = 0 := by
  funext k i
  simp [hilbertCoeff, extendFiniteState]

theorem hilbertCoeff_support (N : ℕ) (z : GalerkinHilbertState N)
    (k : Frequency) (hk : k ∉ cutoffModes N) (i : Fin 3) :
    hilbertCoeff N z k i = 0 := by
  simp [hilbertCoeff, extendFiniteState, hk]

theorem hilbertCoeff_apply (N : ℕ) (z : GalerkinHilbertState N)
    (k : ↥(cutoffModes N)) (i : Fin 3) :
    hilbertCoeff N z k.val i = z (k, i) := by
  simp [hilbertCoeff, extendFiniteState, k.property]

/-- The actual real, divergence-free finite Fourier subspace. -/
def invariantGalerkinSubspace (N : ℕ) : Submodule ℝ (GalerkinHilbertState N) where
  carrier := {z | SpectralReality (hilbertCoeff N z) ∧
    SpectralSolenoidal (hilbertCoeff N z)}
  zero_mem' := by
    change SpectralReality (hilbertCoeff N 0) ∧ SpectralSolenoidal (hilbertCoeff N 0)
    rw [hilbertCoeff_zero]
    constructor
    · intro k i
      simp
    · intro k
      simp
  add_mem' := by
    intro z w hz hw
    change SpectralReality (hilbertCoeff N (z + w)) ∧
      SpectralSolenoidal (hilbertCoeff N (z + w))
    rw [hilbertCoeff_add]
    constructor
    · intro k i
      simpa using congrArg₂ (· + ·) (hz.1 k i) (hw.1 k i)
    · intro k
      simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hz.2 k, hw.2 k,
        add_zero] using (add_zero (0 : ℂ))
  smul_mem' := by
    intro r z hz
    change SpectralReality (hilbertCoeff N (r • z)) ∧
      SpectralSolenoidal (hilbertCoeff N (r • z))
    rw [hilbertCoeff_smul]
    constructor
    · intro k i
      simp only [Pi.smul_apply, star_smul, star_trivial, hz.1 k i]
    · intro k
      simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, hz.2 k, smul_zero]

abbrev InvariantGalerkinState (N : ℕ) := invariantGalerkinSubspace N

/-- The ambient polynomial field, written in Hilbert coordinates. -/
def hilbertGalerkinRhs (ν : ℝ) (N : ℕ) (z : GalerkinHilbertState N) :
    GalerkinHilbertState N :=
  WithLp.toLp 2 (fun ki => galerkinRhs ν N (hilbertCoeff N z) ki.1.val ki.2)

theorem hilbertCoeff_rhs (ν : ℝ) (N : ℕ) (z : GalerkinHilbertState N) :
    hilbertCoeff N (hilbertGalerkinRhs ν N z) =
      cutoffCoeff N (galerkinRhs ν N (hilbertCoeff N z)) := by
  funext k i
  by_cases hk : k ∈ cutoffModes N <;>
    simp [hilbertCoeff, hilbertGalerkinRhs, extendFiniteState, cutoffCoeff, hk]

theorem hilbertGalerkinRhs_mem (ν : ℝ) (N : ℕ)
    (z : InvariantGalerkinState N) :
    hilbertGalerkinRhs ν N z.val ∈ invariantGalerkinSubspace N := by
  change SpectralReality (hilbertCoeff N (hilbertGalerkinRhs ν N z.val)) ∧
    SpectralSolenoidal (hilbertCoeff N (hilbertGalerkinRhs ν N z.val))
  rw [hilbertCoeff_rhs]
  exact ⟨cutoffCoeff_preserves_reality N (galerkinRhs_reality ν N _ z.property.1),
    cutoffCoeff_preserves_solenoidal N (galerkinRhs_solenoidal ν N _ z.property.2)⟩

theorem contDiff_hilbertGalerkinRhs (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (hilbertGalerkinRhs ν N) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.2
  intro ki
  have hcoords : ContDiff ℝ ∞
      (fun z : GalerkinHilbertState N => fun k : ↥(cutoffModes N) =>
        fun i : Fin 3 => z (k, i)) := by
    apply contDiff_pi.2
    intro k
    apply contDiff_pi.2
    intro i
    exact (contDiff_apply ℝ ℂ (k, i)).comp PiLp.contDiff_ofLp
  exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_finiteGalerkinRhs ν N) ki.1) ki.2).comp hcoords

/-- The intrinsic field on the invariant state space. The projection below is
equal to the original polynomial field because tangency was proved above. -/
def invariantGalerkinRhs (ν : ℝ) (N : ℕ) :
    InvariantGalerkinState N → InvariantGalerkinState N :=
  fun z => (invariantGalerkinSubspace N).orthogonalProjectionOnto
    (hilbertGalerkinRhs ν N z.val)

theorem invariantGalerkinRhs_coe (ν : ℝ) (N : ℕ) (z : InvariantGalerkinState N) :
    (invariantGalerkinRhs ν N z).val = hilbertGalerkinRhs ν N z.val := by
  exact (invariantGalerkinSubspace N).starProjection_eq_self_iff.mpr
    (hilbertGalerkinRhs_mem ν N z)

theorem contDiff_invariantGalerkinRhs (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (invariantGalerkinRhs ν N) := by
  exact (invariantGalerkinSubspace N).orthogonalProjectionOnto.contDiff.comp
    ((contDiff_hilbertGalerkinRhs ν N).comp
      (invariantGalerkinSubspace N).subtypeL.contDiff)

/-- The intrinsic Hilbert pairing is exactly the concrete finite Fourier
energy pairing, with no change of nonlinear vector field. -/
theorem invariantGalerkinRhs_inner (ν : ℝ) (N : ℕ) (z : InvariantGalerkinState N) :
    inner (𝕜 := ℝ) z (invariantGalerkinRhs ν N z) =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k i).re := by
  change inner (𝕜 := ℝ) z.val (invariantGalerkinRhs ν N z).val = _
  rw [invariantGalerkinRhs_coe, PiLp.inner_apply]
  simp only [Complex.inner, ← Complex.star_def, Fintype.sum_prod_type]
  change (∑ k : ↥(cutoffModes N), ∑ i : Fin 3,
    (galerkinRhs ν N (hilbertCoeff N z.val) k.val i * star (z.val (k, i))).re) = _
  calc
    _ = ∑ k : ↥(cutoffModes N), ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k.val i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k.val i).re := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw [hilbertCoeff_apply]
      congr 1
      exact mul_comm _ _
    _ = _ := Finset.sum_coe_sort (cutoffModes N)
      (fun k => ∑ i : Fin 3,
        (star (hilbertCoeff N z.val k i) *
          galerkinRhs ν N (hilbertCoeff N z.val) k i).re)

/-- Actual Navier--Stokes dissipation on the invariant finite Fourier space. -/
theorem invariantGalerkinRhs_dissipative (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ)
    (z : InvariantGalerkinState N) :
    inner (𝕜 := ℝ) z (invariantGalerkinRhs ν N z) ≤ 0 := by
  rw [invariantGalerkinRhs_inner]
  have hz := coefficientNonlinearPower_eq_zero N (hilbertCoeff N z.val)
    (hilbertCoeff_support N z.val) z.property.1 z.property.2
  have hr := coefficientEnergy_rate_split ν N (hilbertCoeff N z.val)
  rw [hz, mul_zero, sub_zero] at hr
  simp only [← Finset.mul_sum] at hr
  have hd := coefficientDissipation_nonneg N (hilbertCoeff N z.val)
  have hνd := mul_nonneg hν hd
  nlinarith

/-- Global forward existence on the actual invariant Fourier state space. -/
theorem invariantGalerkinRhs_global_exists (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ)
    (z₀ : InvariantGalerkinState N) :
    ∃ z : ℝ → InvariantGalerkinState N, z 0 = z₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt z (invariantGalerkinRhs ν N (z t)) t := by
  exact forwardGlobalSolution_exists (invariantGalerkinRhs ν N)
    ((contDiff_invariantGalerkinRhs ν N).of_le (by norm_num))
    (invariantGalerkinRhs_dissipative ν hν N) z₀

/-- A single intrinsic derivative supplies every retained coefficient's
derivative in the original Fourier ODE. -/
theorem invariantGalerkin_curve_coefficient_deriv
    (ν : ℝ) (N : ℕ) (z : ℝ → InvariantGalerkinState N) (t : ℝ)
    (hz : HasDerivAt z (invariantGalerkinRhs ν N (z t)) t)
    (k : Frequency) (hk : k ∈ cutoffModes N) (i : Fin 3) :
    HasDerivAt (fun s => hilbertCoeff N (z s).val k i)
      (galerkinRhs ν N (hilbertCoeff N (z t).val) k i) t := by
  have hambient := coe_hasDerivAt (invariantGalerkinSubspace N) z _ t hz
  have hcoord :=
    ((EuclideanSpace.proj (𝕜 := ℂ) ((⟨k, hk⟩ : ↥(cutoffModes N)), i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hambient
  change HasDerivAt (fun s => (z s).val ((⟨k, hk⟩ : ↥(cutoffModes N)), i))
    ((invariantGalerkinRhs ν N (z t)).val ((⟨k, hk⟩ : ↥(cutoffModes N)), i)) t at hcoord
  rw [invariantGalerkinRhs_coe] at hcoord
  change HasDerivAt (fun s => (z s).val ((⟨k, hk⟩ : ↥(cutoffModes N)), i))
    (galerkinRhs ν N (hilbertCoeff N (z t).val) k i) t at hcoord
  have hfun : (fun s => hilbertCoeff N (z s).val k i) =
      (fun s => (z s).val ((⟨k, hk⟩ : ↥(cutoffModes N)), i)) := by
    funext s
    exact hilbertCoeff_apply N (z s).val ⟨k, hk⟩ i
  rw [hfun]
  exact hcoord

/-- Global existence from the exact Fourier integrability, reality and
solenoidality identities of a physical datum.  These initial Fourier
identities remain explicit; the global ODE existence is proved here. -/
theorem galerkinSolution_exists_of_fourier_invariants (ν : ℝ) (hν : 0 ≤ ν)
    (a : Field) (N : ℕ)
    (hint : ∀ k : Frequency, ∀ i : Fin 3,
      MeasureTheory.IntegrableOn (datumFourierIntegrand a k i) unitCube MeasureTheory.volume)
    (hreal : SpectralReality (datumFourierCoeff a))
    (hsol : SpectralSolenoidal (datumFourierCoeff a)) :
    Nonempty (GalerkinSolution ν a N) := by
  let zraw : GalerkinHilbertState N :=
    WithLp.toLp 2 (fun ki => datumFourierCoeff a ki.1.val ki.2)
  have hzraw : hilbertCoeff N zraw = cutoffCoeff N (datumFourierCoeff a) := by
    funext k i
    by_cases hk : k ∈ cutoffModes N <;>
      simp [hilbertCoeff, zraw, extendFiniteState, cutoffCoeff, hk]
  have hzmem : zraw ∈ invariantGalerkinSubspace N := by
    change SpectralReality (hilbertCoeff N zraw) ∧ SpectralSolenoidal (hilbertCoeff N zraw)
    rw [hzraw]
    exact ⟨cutoffCoeff_preserves_reality N hreal,
      cutoffCoeff_preserves_solenoidal N hsol⟩
  let z₀ : InvariantGalerkinState N := ⟨zraw, hzmem⟩
  obtain ⟨z, hz0, hzd⟩ := invariantGalerkinRhs_global_exists ν hν N z₀
  refine ⟨{
    coeff := fun t => hilbertCoeff N (z t).val
    coefficient_continuous := ?_
    mode_support := ?_
    real_symmetry := ?_
    solenoidal := ?_
    initial_integrable := hint
    initial := ?_
    equation := ?_
  }⟩
  · intro k i t ht
    by_cases hk : k ∈ cutoffModes N
    · have hd := invariantGalerkin_curve_coefficient_deriv ν N z t (hzd t ht) k hk i
      exact hd.continuousAt.continuousWithinAt
    · have hz : (fun s => hilbertCoeff N (z s).val k i) = fun _ => (0 : ℂ) := by
        funext s
        exact hilbertCoeff_support N (z s).val k hk i
      rw [hz]
      exact continuousWithinAt_const
  · intro t ht k hk i
    exact hilbertCoeff_support N (z t).val k hk i
  · intro t ht
    exact (z t).property.1
  · intro t ht
    exact (z t).property.2
  · intro k i
    rw [hz0]
    change hilbertCoeff N zraw k i = _
    rw [hzraw]
    rfl
  · intro t ht k hk i
    exact (invariantGalerkin_curve_coefficient_deriv ν N z t (hzd t ht) k hk i).hasDerivWithinAt

end

end SingularClosure
