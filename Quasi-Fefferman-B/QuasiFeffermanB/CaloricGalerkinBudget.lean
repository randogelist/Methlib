import QuasiFeffermanB.CaloricMultiplier
import QuasiFeffermanB.CaloricConvolution
import SingularClosure.StrongAccumulation

/-! Literal integrating-factor identities for the finite Galerkin system.
No Duhamel identity is accepted as an external admission. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem REAL_SCALAR_DUHAMEL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (α T : ℝ) (u f : ℝ → E) (hT : 0 ≤ T)
    (hu : ContinuousOn u (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hdu : ∀ t ∈ Ioo 0 T, HasDerivAt u (f t - α • u t) t) :
    u T = Real.exp (-α * T) • u 0 +
      ∫ s in (0 : ℝ)..T, Real.exp (-α * (T - s)) • f s := by
  let D : ℝ → E := fun t => Real.exp (α * t) • u t
  have he : Continuous (fun t : ℝ => Real.exp (α * t)) := by fun_prop
  have hDc : ContinuousOn D (Icc 0 T) := he.continuousOn.smul hu
  have hDd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt D (Real.exp (α * t) • f t) t := by
    have h := (((hasDerivAt_id t).const_mul α).exp).smul (hdu t ht)
    apply h.congr_deriv
    change Real.exp (α * t) • (f t - α • u t) +
        (Real.exp (α * t) * (α * 1)) • u t = Real.exp (α * t) • f t
    simp only [smul_sub, smul_smul, mul_one]
    abel
  have hFi : IntervalIntegrable (fun t => Real.exp (α * t) • f t) volume 0 T :=
    (he.continuousOn.smul hf).intervalIntegrable_of_Icc hT
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hDc hDd hFi
  have hc : Real.exp (-α * T) * Real.exp (α * T) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hmul := congrArg (fun z : E => Real.exp (-α * T) • z) hFTC
  simp only [D, mul_zero, Real.exp_zero, one_smul, smul_sub, smul_smul, hc] at hmul
  have hkernel : Real.exp (-α * T) •
      (∫ s in (0 : ℝ)..T, Real.exp (α * s) • f s) =
      ∫ s in (0 : ℝ)..T, Real.exp (-α * (T - s)) • f s := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    change Real.exp (-α * T) • (Real.exp (α * s) • f s) =
      Real.exp (-α * (T - s)) • f s
    rw [smul_smul, ← Real.exp_add]
    congr 2 <;> ring
  rw [hkernel] at hmul
  calc
    u T = Real.exp (-α * T) • u 0 + (u T - Real.exp (-α * T) • u 0) := by abel
    _ = _ := by rw [← hmul]

def complexUnit (i : Fin 3) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (Pi.single i 1)

theorem complexVec_sum_units (c : Fin 3 → ℂ) :
    complexVec c = ∑ i : Fin 3, c i • complexUnit i := by
  ext j
  fin_cases j <;> simp [complexVec, complexUnit, Fin.sum_univ_succ, Pi.single_apply]

theorem GALERKIN_COMPLEX_MODE_CONTINUOUS
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) (k : Frequency) :
    ContinuousOn (fun t => complexVec (g.coeff t k)) (Ici 0) := by
  simp_rw [complexVec_sum_units]
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact (g.coefficient_continuous k i).smul continuousOn_const

theorem GALERKIN_COMPLEX_MODE_HAS_DERIV
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (hk : k ∈ cutoffModes N) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => complexVec (g.coeff r k))
      (complexVec (galerkinRhs ν N (g.coeff t) k)) t := by
  simp_rw [complexVec_sum_units]
  apply HasDerivAt.fun_sum
  intro i _
  exact ((g.equation t ht.le k hk i).hasDerivAt (Ici_mem_nhds ht)).smul_const (complexUnit i)

theorem GALERKIN_COMPLEX_FORCING_CONTINUOUS
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (hk : k ∈ cutoffModes N) :
    ContinuousOn (fun t => -complexVec (coefficientLeray k (coefficientTransport N (g.coeff t) k)))
      (Ici 0) := by
  have hR : ContinuousOn (fun t => complexVec (galerkinRhs ν N (g.coeff t) k)) (Ici 0) := by
    simp_rw [complexVec_sum_units]
    apply continuousOn_finsetSum Finset.univ
    intro i _
    exact (g.rhs_continuousOn hk i).smul continuousOn_const
  have h := hR.add ((GALERKIN_COMPLEX_MODE_CONTINUOUS g k).const_smul
    (ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)))
  apply h.congr
  intro t _
  ext i
  change -coefficientLeray k (coefficientTransport N (g.coeff t) k) i =
    -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * g.coeff t k i -
      coefficientLeray k (coefficientTransport N (g.coeff t) k) i +
        ((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * g.coeff t k i
  ring

/-- The actual finite NSE mode satisfies its heat-semigroup Duhamel formula. -/
theorem GALERKIN_MODE_DUHAMEL
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (k : Frequency) (hk : k ∈ cutoffModes N) (T : ℝ) (hT : 0 ≤ T) :
    complexVec (g.coeff T k) =
      Real.exp (-(ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * T) •
        complexVec (g.coeff 0 k) +
      ∫ s in (0 : ℝ)..T,
        Real.exp (-(ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) * (T - s)) •
          (-complexVec (coefficientLeray k (coefficientTransport N (g.coeff s) k))) := by
  apply REAL_SCALAR_DUHAMEL _ T _ _ hT
    ((GALERKIN_COMPLEX_MODE_CONTINUOUS g k).mono (fun t ht => ht.1))
    ((GALERKIN_COMPLEX_FORCING_CONTINUOUS g k hk).mono (fun t ht => ht.1))
  intro t ht
  apply (GALERKIN_COMPLEX_MODE_HAS_DERIV g k hk t ht.1).congr_deriv
  apply PiLp.ext
  intro i
  change -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * g.coeff t k i -
      coefficientLeray k (coefficientTransport N (g.coeff t) k) i =
    -coefficientLeray k (coefficientTransport N (g.coeff t) k) i -
      ((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * g.coeff t k i
  ring

end
end QuasiFeffermanB
