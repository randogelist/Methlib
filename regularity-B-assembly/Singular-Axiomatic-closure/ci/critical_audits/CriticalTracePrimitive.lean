import SingularClosure.CriticalTracePrimitive

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (a : CriticalSobolev 1)
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
        w t = criticalSobolevLower 1 3 (by norm_num) (u t)) :=
  @SingularClosure.CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION a u v T hT hu hv hevolution

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION"
#check @SingularClosure.CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION
#print axioms SingularClosure.CRITICAL_HHALF_STRONG_TRACE_OF_INTEGRAL_EVOLUTION

end
end SingularClosure
