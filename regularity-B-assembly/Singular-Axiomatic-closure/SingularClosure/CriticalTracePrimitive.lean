import SingularClosure.CriticalTraceStrong

/-! Strong trace directly from the literal coefficient integral evolution. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Interval

namespace SingularClosure

noncomputable section

/-- The canonical time primitive, written in real coordinates. -/
def criticalTracePrimitiveCoeff (a : CriticalSobolev 1)
    (v : ℝ → CriticalSobolev (-1)) : ℝ → FourierCoeff :=
  fun t k i =>
    (((criticalCoeff 1 a k i).re +
      ∫ τ in (0 : ℝ)..t, (criticalCoeff (-1) (v τ) k i).re : ℝ) : ℂ) +
    (((criticalCoeff 1 a k i).im +
      ∫ τ in (0 : ℝ)..t, (criticalCoeff (-1) (v τ) k i).im : ℝ) : ℂ) * Complex.I

@[simp]
theorem criticalTracePrimitiveCoeff_initial (a : CriticalSobolev 1)
    (v : ℝ → CriticalSobolev (-1)) :
    criticalTracePrimitiveCoeff a v 0 = criticalCoeff 1 a := by
  funext k i
  simp only [criticalTracePrimitiveCoeff, intervalIntegral.integral_same, add_zero,
    Complex.re_add_im]

private theorem criticalTrace_ac_const (a b z : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b := by
  simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
  exact tendsto_const_nhds

theorem criticalTracePrimitive_integrable_coords
    (v : ℝ → CriticalSobolev (-1)) {T : ℝ} (hT : 0 ≤ T)
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T))) (k : Frequency) (i : Fin 3) :
    IntervalIntegrable (fun t => (criticalCoeff (-1) (v t) k i).re) volume 0 T ∧
      IntervalIntegrable (fun t => (criticalCoeff (-1) (v t) k i).im) volume 0 T := by
  have hcoeff : MemLp (fun t => criticalCoeff (-1) (v t) k i) 2
      (volume.restrict (Icc (0 : ℝ) T)) := by
    simpa only [Function.comp_def, criticalSobolevCoeff_apply] using
      (criticalSobolevCoeff (-1) k i).comp_memLp' hv
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
    exact MemLp.integrable (by norm_num) (Complex.reCLM.comp_memLp' hcoeff)
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
    exact MemLp.integrable (by norm_num) (Complex.imCLM.comp_memLp' hcoeff)

/-- Coordinate absolute continuity is discharged by the coefficient primitive. -/
theorem criticalTracePrimitive_absolutelyContinuous
    (a : CriticalSobolev 1) (v : ℝ → CriticalSobolev (-1))
    {T : ℝ} (hT : 0 ≤ T)
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T))) (k : Frequency) (i : Fin 3) :
    AbsolutelyContinuousOnInterval (fun t => (criticalTracePrimitiveCoeff a v t k i).re) 0 T ∧
      AbsolutelyContinuousOnInterval (fun t => (criticalTracePrimitiveCoeff a v t k i).im) 0 T := by
  have hI := criticalTracePrimitive_integrable_coords v hT hv k i
  constructor
  · simpa [criticalTracePrimitiveCoeff] using
      (criticalTrace_ac_const 0 T (criticalCoeff 1 a k i).re).fun_add
        (hI.1.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)
  · simpa [criticalTracePrimitiveCoeff] using
      (criticalTrace_ac_const 0 T (criticalCoeff 1 a k i).im).fun_add
        (hI.2.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)

/-- The primitive has the given H^(-1/2) derivative in every Fourier coordinate. -/
theorem criticalTracePrimitive_ae_hasDerivAt
    (a : CriticalSobolev 1) (v : ℝ → CriticalSobolev (-1))
    {T : ℝ} (hT : 0 ≤ T)
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T))) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ k i,
      HasDerivAt (fun τ => criticalTracePrimitiveCoeff a v τ k i)
        (criticalCoeff (-1) (v t) k i) t := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro i
  have hI := criticalTracePrimitive_integrable_coords v hT hv k i
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hI.1.ae_hasDerivAt_integral, hI.2.ae_hasDerivAt_integral]
    with t htR htI ht
  have ht' : t ∈ uIcc (0 : ℝ) T := by simpa only [uIcc_of_le hT] using ht
  have hR := (htR ht' 0 left_mem_uIcc).const_add (criticalCoeff 1 a k i).re
  have hIm := (htI ht' 0 left_mem_uIcc).const_add (criticalCoeff 1 a k i).im
  simpa only [criticalTracePrimitiveCoeff, Complex.re_add_im] using
    hR.ofReal_comp.fun_add (hIm.ofReal_comp.mul_const Complex.I)

/-- Integral coefficient evolution and the two Bochner L2 bounds imply the strong trace.

The coefficient evolution identifies the canonical primitive with the H^(3/2)
representative almost everywhere. No temporal continuity premise remains. -/
theorem CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION
    (a : CriticalSobolev 1)
    (u : ℝ → CriticalSobolev 3) (v : ℝ → CriticalSobolev (-1))
    {T : ℝ} (hT : 0 < T)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hevolution : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalTracePrimitiveCoeff a v t = criticalCoeff 3 (u t)) :
    ∃ w : ℝ → CriticalSobolev 1,
      ContinuousOn w (Icc (0 : ℝ) T) ∧ w 0 = a ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        criticalCoeff 1 (w t) = criticalTracePrimitiveCoeff a v t) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        w t = criticalSobolevLower 1 3 (by norm_num) (u t)) := by
  exact CRITICAL_HHALF_STRONG_TRACE (criticalTracePrimitiveCoeff a v)
    (fun t => criticalCoeff (-1) (v t)) u v hT
    (fun k i => (criticalTracePrimitive_absolutelyContinuous a v hT.le hv k i).1)
    (fun k i => (criticalTracePrimitive_absolutelyContinuous a v hT.le hv k i).2)
    (criticalTracePrimitive_ae_hasDerivAt a v hT.le hv) hu hv hevolution
    (Filter.Eventually.of_forall fun _ => rfl) a (criticalTracePrimitiveCoeff_initial a v)

end

end SingularClosure
