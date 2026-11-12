import SingularityDisprovement.Dirichlet
import SingularityDisprovement.Dyadic
import SingularityDisprovement.Physical
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact identification of the native dyadic datum with its ordinary cosine
series representative. All assertions concern the actual physical L2 class. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators Topology ENNReal

namespace SingularityDisprovement
noncomputable section

private theorem dyadic_synthesis_axis_of_ne_zero (ν : ℝ) (x : Vec)
    (i : Fin 3) (k : Frequency)
    (h : (fourierCharacter k x * dyadicCoeff ν k i).re ≠ 0) :
    k 0 = 0 ∧ k 2 = 0 := by
  by_contra hk
  have h' : ¬ (i = 0 ∧ k 0 = 0 ∧ k 2 = 0) := by
    tauto
  simp [dyadicCoeff, h'] at h

theorem dyadic_finite_synthesis_reindex (ν : ℝ) (N : ℕ) (x : Vec) (i : Fin 3) :
    (∑ k ∈ cutoffModes N, (fourierCharacter k x * dyadicCoeff ν k i).re) =
      ∑ z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fourierCharacter (shearFrequency z) x * dyadicCoeff ν (shearFrequency z) i).re := by
  classical
  apply Finset.sum_bij_ne_zero (fun k _ _ => k 1)
  · intro k hk hkn
    exact Finset.mem_Icc.mpr (((mem_cutoffModes_iff N k).mp hk).1 1)
  · intro k hk hkn l hl hln hkl
    have hka := dyadic_synthesis_axis_of_ne_zero ν x i k hkn
    have hla := dyadic_synthesis_axis_of_ne_zero ν x i l hln
    calc
      k = shearFrequency (k 1) := (shearFrequency_of_axis hka.1 hka.2).symm
      _ = shearFrequency (l 1) := congrArg shearFrequency hkl
      _ = l := shearFrequency_of_axis hla.1 hla.2
  · intro z hz hzn
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      simp [dyadicCoeff] at hzn
    have hbounds := Finset.mem_Icc.mp hz
    have hmem : shearFrequency z ∈ cutoffModes N := by
      apply (mem_cutoffModes_iff N _).mpr
      refine ⟨?_, shearFrequency_ne_zero hz0, ?_⟩
      · intro j
        fin_cases j <;> simp only [shearFrequency_apply_zero,
          shearFrequency_apply_one, shearFrequency_apply_two]
        · constructor <;> omega
        · exact hbounds
        · constructor <;> omega
      · have hprod : 0 ≤ ((N : ℤ) - z) * ((N : ℤ) + z) :=
          mul_nonneg (by omega) (by omega)
        have hs : galerkinFreqSq (shearFrequency z) = z ^ 2 := by
          simp [galerkinFreqSq, shearFrequency, Fin.sum_univ_succ]
        rw [hs]
        nlinarith
    exact ⟨shearFrequency z, hmem, hzn, rfl⟩
  · intro k hk hkn
    have hka := dyadic_synthesis_axis_of_ne_zero ν x i k hkn
    rw [shearFrequency_of_axis hka.1 hka.2]

theorem fourierCharacter_shear_re (z : ℤ) (x : Vec) :
    (fourierCharacter (shearFrequency z) x).re =
      Real.cos ((z : ℝ) * (2 * Real.pi * x 1)) := by
  unfold fourierCharacter
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  simp [shearFrequency, Fin.sum_univ_succ]
  ring

theorem dyadic_synthesis_axis_term (ν : ℝ) (z : ℤ) (x : Vec) (i : Fin 3) :
    (fourierCharacter (shearFrequency z) x * dyadicCoeff ν (shearFrequency z) i).re =
      if i = 0 then
        (ν / 4 * dyadicAmplitude z.natAbs) * Real.cos ((z : ℝ) * (2 * Real.pi * x 1))
      else 0 := by
  by_cases hi : i = 0
  · subst i
    rw [dyadicCoeff_axis]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, if_true, fourierCharacter_shear_re]
    ring
  · simp [dyadicCoeff, hi]

theorem dyadic_finite_synthesis_component (ν : ℝ) (N : ℕ) (x : Vec) (i : Fin 3) :
    finiteSynthesis N (dyadicCoeff ν) x i =
      if i = 0 then (ν / 2) * dyadicCosinePartial (N + 1) (x 1) else 0 := by
  classical
  change (∑ k ∈ cutoffModes N, fourierCharacter k x * dyadicCoeff ν k i).re = _
  rw [Complex.re_sum, dyadic_finite_synthesis_reindex]
  simp_rw [dyadic_synthesis_axis_term]
  by_cases hi : i = 0
  · simp only [hi, if_true]
    let f : ℤ → ℝ := fun z =>
      (ν / 4 * dyadicAmplitude z.natAbs) * Real.cos ((z : ℝ) * (2 * Real.pi * x 1))
    have hf : f.Even := by
      intro z
      simp [f, Int.natAbs_neg, neg_mul, Real.cos_neg]
    have hsum := Finset.sum_Icc_of_even_eq_range hf N
    change (∑ z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f z) = _
    rw [hsum]
    simp only [f, Int.natAbs_natCast, Int.cast_natCast, Int.natAbs_zero,
      dyadicAmplitude_zero, mul_zero, zero_mul, sub_zero, two_nsmul]
    unfold dyadicCosinePartial
    simp_rw [mul_assoc, ← Finset.mul_sum]
    ring
  · simp [hi]

def dyadicPhysicalRepresentative (ν : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i = 0 then (ν / 2) * dyadicCosineValue (x 1) else 0)

theorem ae_second_coordinate_not_int :
    ∀ᵐ x : Vec ∂volume.restrict unitCube, ∀ k : ℤ, x 1 ≠ (k : ℝ) := by
  have hpi : ∀ᵐ x : Fin 3 → ℝ ∂volume, ∀ k : ℤ, x 1 ≠ (k : ℝ) := by
    change ∀ᵐ x : Fin 3 → ℝ ∂Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)),
      ∀ k : ℤ, x 1 ≠ (k : ℝ)
    exact ae_all_iff.mpr (fun k => Measure.ae_eval_ne
      (fun _ : Fin 3 => (volume : Measure ℝ)) 1 (k : ℝ))
  have hv : ∀ᵐ x : Vec ∂volume, ∀ k : ℤ, x 1 ≠ (k : ℝ) :=
    (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae hpi
  exact ae_restrict_of_ae hv

theorem dyadic_finite_synthesis_tendsto_ae (ν : ℝ) :
    ∀ᵐ x : Vec ∂volume.restrict unitCube,
      Tendsto (fun N : ℕ => finiteSynthesis N (dyadicCoeff ν) x)
        atTop (𝓝 (dyadicPhysicalRepresentative ν x)) := by
  filter_upwards [ae_second_coordinate_not_int] with x hx
  have hs := (tendsto_add_atTop_iff_nat 1).mpr (dyadicCosine_tendsto (x 1) hx)
  have hcoords : Tendsto
      (fun N : ℕ => fun i : Fin 3 =>
        if i = 0 then (ν / 2) * dyadicCosinePartial (N + 1) (x 1) else 0)
      atTop (𝓝 (fun i : Fin 3 =>
        if i = 0 then (ν / 2) * dyadicCosineValue (x 1) else 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : i = 0
    · simpa only [hi, if_true] using tendsto_const_nhds.mul hs
    · simpa only [hi, if_false] using tendsto_const_nhds
  have h := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp hcoords
  have heq : (fun N : ℕ => finiteSynthesis N (dyadicCoeff ν) x) =
      (fun N : ℕ => WithLp.toLp 2 (fun i : Fin 3 =>
        if i = 0 then (ν / 2) * dyadicCosinePartial (N + 1) (x 1) else 0)) := by
    funext N
    ext i
    exact dyadic_finite_synthesis_component ν N x i
  rw [heq]
  exact h

theorem DYADIC_PHYSICAL_IDENTIFICATION (ν : ℝ) :
    (physicalL2 (dyadicSeed ν) : Field) =ᵐ[volume.restrict unitCube]
      dyadicPhysicalRepresentative ν := by
  have h := physicalCutoff_ae_limit_unique (dyadicSeed ν)
    (dyadicSeed_sigma ν).reality (dyadicSeed_sigma ν).mean_zero
    (dyadicPhysicalRepresentative ν) (by simpa using dyadic_finite_synthesis_tendsto_ae ν)
  exact h

end
end SingularityDisprovement
