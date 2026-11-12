import QuasiFeffermanB.CaloricMultiplier
import SingularClosure.FourierSobolevOperators
import SingularClosure.GalerkinEnergy
import SingularClosure.CriticalSpaces

/-! Exact finite Fourier symmetrization for the actual Galerkin transport.
All vector norms in this module are Hermitian Euclidean norms. -/

set_option autoImplicit false
set_option Elab.async true
noncomputable section
open SingularClosure
open scoped BigOperators

namespace QuasiFeffermanB

def frequencyDot (k : Frequency) (z : Fin 3 → ℂ) : ℂ :=
  ∑ j : Fin 3, z j * (k j : ℂ)

def symmetricFrequencyTensor (k : Frequency) (z w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => frequencyDot k z * w i + frequencyDot k w * z i

def modeLerayLinear (k : Frequency) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun := coefficientLeray k
  map_add' := coefficientLeray_add_arg k
  map_smul' := coefficientLeray_smul_arg k

theorem complexVecNorm_finset_sum_le {ι : Type*} (S : Finset ι)
    (v : ι → Fin 3 → ℂ) :
    complexVecNorm (fun i => ∑ p ∈ S, v p i) ≤ ∑ p ∈ S, complexVecNorm (v p) := by
  have heq : complexVec (fun i => ∑ p ∈ S, v p i) = ∑ p ∈ S, complexVec (v p) := by
    ext i
    simp [complexVec]
  simp_rw [complexVecNorm_eq_norm]
  rw [heq]
  exact norm_sum_le _ _

theorem coefficientTransport_frequencyDot (N : ℕ) (c : FourierCoeff)
    (hsol : SpectralSolenoidal c) (k : Frequency) (i : Fin 3) :
    coefficientTransport N c k i =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        ∑ p ∈ cutoffModes N, frequencyDot k (c p) * c (k - p) i := by
  have hterm (p : Frequency) :
      (∑ j : Fin 3, c p j *
        (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * frequencyDot k (c p) := by
    have hfactor :
        (∑ j : Fin 3, c p j *
          (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            transportFrequencyPairing c p (k - p) := by
      rw [transportFrequencyPairing, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.sub_apply]
      push_cast
      ring
    rw [hfactor, transportFrequencyPairing_sub,
      transportFrequencyPairing_self c p (hsol p), sub_zero]
    rfl
  simp only [coefficientTransport, hterm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem finite_convolution_swap (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ i : Fin 3, c p i = 0)
    (k : Frequency) (i : Fin 3) :
    (∑ p ∈ cutoffModes N, frequencyDot k (c p) * c (k - p) i) =
      ∑ p ∈ cutoffModes N, frequencyDot k (c (k - p)) * c p i := by
  classical
  let S := (cutoffModes N).filter (fun p => k - p ∈ cutoffModes N)
  have hF : (∑ p ∈ S, frequencyDot k (c p) * c (k - p) i) =
      ∑ p ∈ cutoffModes N, frequencyDot k (c p) * c (k - p) i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hkp : k - p ∉ cutoffModes N := fun h => hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
    rw [hsupp (k - p) hkp i, mul_zero]
  have hG : (∑ p ∈ S, frequencyDot k (c (k - p)) * c p i) =
      ∑ p ∈ cutoffModes N, frequencyDot k (c (k - p)) * c p i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hkp : k - p ∉ cutoffModes N := fun h => hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
    simp only [frequencyDot, hsupp (k - p) hkp, zero_mul, Finset.sum_const_zero]
  have hmem (p : Frequency) (hp : p ∈ S) : k - p ∈ S := by
    obtain ⟨hp, hkp⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hkp, ?_⟩
    have heq : k - (k - p) = p := by abel
    rwa [heq]
  have hswap : (∑ p ∈ S, frequencyDot k (c p) * c (k - p) i) =
      ∑ p ∈ S, frequencyDot k (c (k - p)) * c p i := by
    apply Finset.sum_nbij' (fun p => k - p) (fun p => k - p) hmem hmem
    · intro p _
      abel
    · intro p _
      abel
    · intro p _
      have heq : k - (k - p) = p := by abel
      rw [heq]
  rwa [hF, hG] at hswap

theorem coefficientTransport_symmetric (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ i : Fin 3, c p i = 0)
    (hsol : SpectralSolenoidal c) (k : Frequency) :
    coefficientTransport N c k =
      ((Real.pi : ℂ) * Complex.I) •
        ∑ p ∈ cutoffModes N, symmetricFrequencyTensor k (c p) (c (k - p)) := by
  funext i
  rw [coefficientTransport_frequencyDot N c hsol k i]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    symmetricFrequencyTensor, Finset.sum_add_distrib]
  rw [← finite_convolution_swap N c hsupp k i]
  push_cast
  ring

theorem coefficientLeray_transport_symmetric (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ p : Frequency, p ∉ cutoffModes N → ∀ i : Fin 3, c p i = 0)
    (hsol : SpectralSolenoidal c) (k : Frequency) :
    coefficientLeray k (coefficientTransport N c k) =
      ((Real.pi : ℂ) * Complex.I) •
        ∑ p ∈ cutoffModes N,
          coefficientLeray k (symmetricFrequencyTensor k (c p) (c (k - p))) := by
  rw [coefficientTransport_symmetric N c hsupp hsol k]
  change modeLerayLinear k _ = _
  rw [map_smul, map_sum]
  rfl

end QuasiFeffermanB
