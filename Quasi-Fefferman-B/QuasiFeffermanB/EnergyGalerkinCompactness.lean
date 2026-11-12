import SingularClosure.CriticalLimit
import SingularClosure.FourierLimitEquation
import SingularClosure.FourierSobolevOperators

/-! Energy-level Fourier compactness. The only trajectory hypothesis in the
principal theorem is a uniform initial L2 energy bound for actual Galerkin
solutions. No positive Sobolev bound or regularity certificate is assumed.
-/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology BigOperators Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- The literal finite-dimensional Leray projection as a bounded linear map. -/
def energyModeLeray (k : Frequency) :
    (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) where
  toFun := coefficientLeray k
  map_add' := coefficientLeray_add_arg k
  map_smul' := coefficientLeray_smul_arg k
  cont := (contDiff_coefficientLeray k).continuous

def energyModeTransportBound (k : Frequency) : ℝ :=
  ∑ j : Fin 3, ‖divergenceTransportCoefficient k j‖

theorem energyModeTransportBound_nonneg (k : Frequency) :
    0 ≤ energyModeTransportBound k :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem energyModeTransport_norm_le (k : Frequency) (c : TorusSobolev 0) :
    ‖fun j : Fin 3 => divergenceTransportCoefficient k j c c‖ ≤
      energyModeTransportBound k * ‖c‖ ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (energyModeTransportBound_nonneg k)
    (sq_nonneg ‖c‖))).mpr
  intro j
  calc
    _ ≤ ‖divergenceTransportCoefficient k j c‖ * ‖c‖ :=
      (divergenceTransportCoefficient k j c).le_opNorm c
    _ ≤ (‖divergenceTransportCoefficient k j‖ * ‖c‖) * ‖c‖ :=
      mul_le_mul_of_nonneg_right
        ((divergenceTransportCoefficient k j).le_opNorm c) (norm_nonneg c)
    _ = ‖divergenceTransportCoefficient k j‖ * ‖c‖ ^ 2 := by ring
    _ ≤ energyModeTransportBound k * ‖c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖c‖)
      exact Finset.single_le_sum (fun i _ => norm_nonneg
        (divergenceTransportCoefficient k i)) (Finset.mem_univ j)

def energyModeRhsBound (ν R : ℝ) (k : Frequency) (i : Fin 3) : ℝ :=
  |ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)| *
      ‖torusSobolevH0Coeff k i‖ * R +
    ‖energyModeLeray k‖ * energyModeTransportBound k * R ^ 2

theorem energyModeRhsBound_nonneg (ν R : ℝ) (hR : 0 ≤ R)
    (k : Frequency) (i : Fin 3) : 0 ≤ energyModeRhsBound ν R k i := by
  unfold energyModeRhsBound
  exact add_nonneg
    (mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hR)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (energyModeTransportBound_nonneg k))
      (sq_nonneg R))

/-- Every fixed actual Fourier RHS is uniformly bounded on an L2 ball. -/
theorem fullFourierRhs_energy_bound (ν R : ℝ) (hR : 0 ≤ R)
    (c : TorusSobolev 0) (hc : ‖c‖ ≤ R) (k : Frequency) (i : Fin 3) :
    ‖fullFourierRhs ν c k i‖ ≤ energyModeRhsBound ν R k i := by
  have hcoeff : ‖c.val k i‖ ≤ ‖torusSobolevH0Coeff k i‖ * R := by
    rw [← torusSobolevH0Coeff_apply]
    exact ((torusSobolevH0Coeff k i).le_opNorm c).trans
      (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  have htransport :
      ‖coefficientLeray k (fun j => divergenceTransportCoefficient k j c c) i‖ ≤
        ‖energyModeLeray k‖ * energyModeTransportBound k * R ^ 2 := by
    calc
      _ ≤ ‖energyModeLeray k (fun j => divergenceTransportCoefficient k j c c)‖ :=
        norm_le_pi_norm _ i
      _ ≤ ‖energyModeLeray k‖ *
          ‖fun j : Fin 3 => divergenceTransportCoefficient k j c c‖ :=
        (energyModeLeray k).le_opNorm _
      _ ≤ ‖energyModeLeray k‖ * (energyModeTransportBound k * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (energyModeTransport_norm_le k c) (norm_nonneg _)
      _ ≤ ‖energyModeLeray k‖ * (energyModeTransportBound k * R ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2)
            (energyModeTransportBound_nonneg k)) (norm_nonneg _)
      _ = _ := by ring
  unfold fullFourierRhs energyModeRhsBound
  calc
    _ ≤ ‖-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
        c.val k i‖ +
        ‖coefficientLeray k (fun j => divergenceTransportCoefficient k j c c) i‖ :=
      norm_sub_le _ _
    _ = |ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)| * ‖c.val k i‖ +
        ‖coefficientLeray k (fun j => divergenceTransportCoefficient k j c c) i‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)| *
        (‖torusSobolevH0Coeff k i‖ * R) +
        ‖energyModeLeray k‖ * energyModeTransportBound k * R ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)) htransport
    _ = _ := by ring

theorem galerkin_H0_norm_sq {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) :
    ‖g.sobolevState 0 t‖ ^ 2 = coefficientEnergy N (g.coeff t) := by
  unfold GalerkinSolution.sobolevState
  rw [finiteSobolev_norm_sq]
  simp only [pow_zero, one_mul, coefficientEnergy]

theorem galerkin_H0_energy_bound {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (R : ℝ) (hR : 0 ≤ R)
    (hinit : coefficientEnergy N (g.coeff 0) ≤ R ^ 2)
    (t : ℝ) (ht : 0 ≤ t) : ‖g.sobolevState 0 t‖ ≤ R := by
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [galerkin_H0_norm_sq]
  exact (g.coefficientEnergy_le_initial hν ht).trans hinit

/-- Energy alone controls each coordinate modulus, uniformly in the cutoff. -/
theorem galerkin_energy_coefficient_modulus
    {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : coefficientEnergy N (g.coeff 0) ≤ R ^ 2)
    (k : Frequency) (i : Fin 3) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ‖g.coeff t k i - g.coeff s k i‖ ^ 2 ≤
      (T * energyModeRhsBound ν R k i ^ 2) * (t - s) := by
  let B := energyModeRhsBound ν R k i
  have hB : 0 ≤ B := energyModeRhsBound_nonneg ν R hR k i
  have hlen : 0 ≤ t - s := sub_nonneg.mpr hst
  by_cases hk : k ∈ cutoffModes N
  · have hrhs : ContinuousOn (fun r => galerkinRhs ν N (g.coeff r) k i) (Icc s t) :=
      (g.rhs_continuousOn hk i).mono (fun r hr => hs.trans hr.1)
    have hpoint (r : ℝ) (hr : r ∈ Icc s t) :
        ‖galerkinRhs ν N (g.coeff r) k i‖ ≤ B := by
      rw [← g.fullFourierRhs_eq r (hs.trans hr.1)]
      exact fullFourierRhs_energy_bound ν R hR (g.sobolevState 0 r)
        (galerkin_H0_energy_bound hν g R hR hinit r (hs.trans hr.1)) k i
    have hint : (∫ r in s..t, ‖galerkinRhs ν N (g.coeff r) k i‖ ^ 2) ≤
        (t - s) * B ^ 2 := by
      calc
        _ ≤ ∫ _r in s..t, B ^ 2 :=
          intervalIntegral.integral_mono_on hst
            ((hrhs.norm.pow 2).intervalIntegrable_of_Icc hst) intervalIntegrable_const
            (fun r hr => pow_le_pow_left₀ (norm_nonneg _) (hpoint r hr) 2)
        _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
    have hcs := intervalIntegral_norm_sq_le_length_mul_integral_norm_sq hst hrhs
    rw [g.coefficient_integral_rhs hk i hs hst] at hcs
    calc
      _ ≤ (t - s) * ((t - s) * B ^ 2) :=
        hcs.trans (mul_le_mul_of_nonneg_left hint hlen)
      _ ≤ (t - s) * (T * B ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith : t - s ≤ T) (sq_nonneg B)) hlen
      _ = _ := by ring
  · rw [g.mode_support t (hs.trans hst) k hk i, g.mode_support s hs k hk i]
    simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hT (sq_nonneg _)) hlen

/-- A common coefficient subsequence on each fixed finite horizon follows
from actual Galerkin evolution and an initial L2 bound only. -/
theorem ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ u : FourierIndex → C(Icc (0 : ℝ) T, ℂ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k i,
        TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
          (g (φ n)).coeff t.val k i) (u (k, i)) atTop := by
  let F : FourierIndex → ℕ → C(Icc (0 : ℝ) T, ℂ) := fun ki n =>
    ⟨fun t => (g n).coeff t.val ki.1 ki.2,
      ((g n).coefficient_continuous ki.1 ki.2).comp_continuous
        continuous_subtype_val (fun t => t.property.1)⟩
  let B : FourierIndex → ℝ := fun ki => ‖torusSobolevH0Coeff ki.1 ki.2‖ * R
  let M : FourierIndex → ℝ := fun ki => T * energyModeRhsBound ν R ki.1 ki.2 ^ 2
  have hM (ki : FourierIndex) : 0 ≤ M ki := mul_nonneg hT (sq_nonneg _)
  have hb (ki : FourierIndex) (n : ℕ) (t : Icc (0 : ℝ) T) :
      ‖F ki n t‖ ≤ B ki := by
    have hs := galerkin_H0_energy_bound hν (g n) R hR (hinit n) t.val t.property.1
    have hc := (torusSobolevH0Coeff ki.1 ki.2).le_opNorm ((g n).sobolevState 0 t.val)
    rw [torusSobolevH0Coeff_apply, (g n).sobolevState_coeff 0 t.property.1] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  have hm (ki : FourierIndex) (n : ℕ) (s t : Icc (0 : ℝ) T) :
      ‖F ki n t - F ki n s‖ ^ 2 ≤ M ki * |t.val - s.val| := by
    change ‖(g n).coeff t.val ki.1 ki.2 - (g n).coeff s.val ki.1 ki.2‖ ^ 2 ≤ _
    rcases le_total s.val t.val with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
        galerkin_energy_coefficient_modulus hν (g n) R T hR hT (hinit n)
          ki.1 ki.2 s.property.1 hst t.property.2
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
      exact galerkin_energy_coefficient_modulus hν (g n) R T hR hT (hinit n)
        ki.1 ki.2 t.property.1 hts s.property.2
  obtain ⟨u, φ, hφ, hconv⟩ :=
    critical_countable_coefficient_uniform_subsequence T F B M hM hb hm
  exact ⟨u, φ, hφ, fun k i => hconv (k, i)⟩

end
end QuasiFeffermanB
