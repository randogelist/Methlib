import SingularClosure.SixChannels

/-!
# Extended nonnegative Fourier energies

Pythagoras is valid even when the total energy is infinite. Membership in
an actual Sobolev space requires the resulting extended energy to be finite.
The physical Parseval/derivative realization is not assumed in this file.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators ENNReal

noncomputable section

namespace SingularClosure

def spectralComponentEnergy (w : Frequency → ℝ≥0∞)
    (a : FourierCoeff) (k : Frequency) (c : Fin 3) : ℝ≥0∞ :=
  w k * ENNReal.ofReal (‖a k c‖ ^ 2)

def spectralEnergy (w : Frequency → ℝ≥0∞) (a : FourierCoeff) : ℝ≥0∞ :=
  ∑' k : Frequency, ∑ c : Fin 3, spectralComponentEnergy w a k c

/-- The actual unit-torus Fourier symbol of minus the Laplacian. -/
def frequencySquare (k : Frequency) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ c : Fin 3, (k c : ℝ) ^ 2

def enstrophyWeight (k : Frequency) : ℝ≥0∞ :=
  ENNReal.ofReal (frequencySquare k)

def spectralEnstrophy (a : FourierCoeff) : ℝ≥0∞ :=
  spectralEnergy enstrophyWeight a

theorem spectralComponentEnergy_channel (w : Frequency → ℝ≥0∞)
    (A : Fin 6) (a : FourierCoeff) (k : Frequency) (c : Fin 3) :
    spectralComponentEnergy w (spectralChannel A a) k c =
      if channelOf k c = A then spectralComponentEnergy w a k c else 0 := by
  by_cases h : channelOf k c = A <;>
    simp [spectralComponentEnergy, spectralChannel, h]

theorem spectralComponentEnergy_sum_channels (w : Frequency → ℝ≥0∞)
    (a : FourierCoeff) (k : Frequency) (c : Fin 3) :
    (∑ A : Fin 6, spectralComponentEnergy w (spectralChannel A a) k c) =
      spectralComponentEnergy w a k c := by
  classical
  simp_rw [spectralComponentEnergy_channel]
  simp [eq_comm]

theorem SIX_CHANNEL_SPECTRAL_ENERGY_EQ (w : Frequency → ℝ≥0∞)
    (a : FourierCoeff) :
    (∑ A : Fin 6, spectralEnergy w (spectralChannel A a)) = spectralEnergy w a := by
  classical
  calc
    (∑ A : Fin 6, spectralEnergy w (spectralChannel A a)) =
        ∑' A : Fin 6, ∑' k : Frequency,
          ∑ c : Fin 3, spectralComponentEnergy w (spectralChannel A a) k c := by
            simp [spectralEnergy]
    _ = ∑' k : Frequency, ∑' A : Fin 6,
          ∑ c : Fin 3, spectralComponentEnergy w (spectralChannel A a) k c :=
            ENNReal.tsum_comm
    _ = ∑' k : Frequency, ∑ c : Fin 3,
          ∑ A : Fin 6, spectralComponentEnergy w (spectralChannel A a) k c := by
            apply tsum_congr
            intro k
            simp only [tsum_fintype]
            exact Finset.sum_comm
    _ = spectralEnergy w a := by
      unfold spectralEnergy
      apply tsum_congr
      intro k
      apply Finset.sum_congr rfl
      intro c _
      exact spectralComponentEnergy_sum_channels w a k c

theorem SIX_CHANNEL_SPECTRAL_ENSTROPHY_EQ (a : FourierCoeff) :
    (∑ A : Fin 6, spectralEnstrophy (spectralChannel A a)) = spectralEnstrophy a := by
  exact SIX_CHANNEL_SPECTRAL_ENERGY_EQ enstrophyWeight a

theorem spectralEnergy_channel_le (w : Frequency → ℝ≥0∞)
    (A : Fin 6) (a : FourierCoeff) :
    spectralEnergy w (spectralChannel A a) ≤ spectralEnergy w a := by
  rw [← SIX_CHANNEL_SPECTRAL_ENERGY_EQ w a]
  exact Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ A)

theorem spectralEnergy_channel_finite (w : Frequency → ℝ≥0∞)
    (A : Fin 6) {a : FourierCoeff} (ha : spectralEnergy w a < ⊤) :
    spectralEnergy w (spectralChannel A a) < ⊤ :=
  lt_of_le_of_lt (spectralEnergy_channel_le w A a) ha

end SingularClosure
