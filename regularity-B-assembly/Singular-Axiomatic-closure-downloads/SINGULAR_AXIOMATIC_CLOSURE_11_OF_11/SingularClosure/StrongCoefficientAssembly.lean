import SingularClosure.StrongCoefficientContracts

/-! Assembly of an actual continuous Sobolev trajectory into the strong contract. -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Interval

namespace SingularClosure

noncomputable section

theorem continuousOn_forward_memLp {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : ContinuousOn f (Ici 0)) (T : ℝ) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) := ⟨by simp⟩
  have hc : ContinuousOn f (Icc (0 : ℝ) T) := hf.mono (fun t ht => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply MemLp.of_bound
    (hc.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

theorem NONEMPTY_GLOBAL_STRONG_COEFFICIENT_NSE_OF_CONTINUOUS
    (ν : ℝ) (a : Field) (ha : SmoothSigmaZero a)
    (u : ℝ → TorusSobolev 1) (u2 : ℝ → TorusSobolev 2)
    (v : ℝ → TorusSobolev 0)
    (hu : ContinuousOn u (Ici 0)) (hu2 : ContinuousOn u2 (Ici 0))
    (hv : ContinuousOn v (Ici 0))
    (hinit : u 0 = smoothDatumSobolev 1 a ha.smooth ha.periodic)
    (h2 : ∀ t : ℝ, 0 ≤ t → torusSobolevInclusion 1 (u2 t) = u t)
    (hint : ∀ t : ℝ, 0 ≤ t → torusSobolevInclusion 0 (u t) =
      torusSobolevInclusion 0 (u 0) + ∫ s in (0 : ℝ)..t, v s)
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency, ∀ i : Fin 3,
      (v t).val k i = fullFourierRhs ν (torusSobolevInclusion 0 (u t)) k i)
    (hreal : ∀ t : ℝ, 0 ≤ t → SpectralReality (u t).val)
    (hsol : ∀ t : ℝ, 0 ≤ t → SpectralSolenoidal (u t).val)
    (hzero : ∀ t : ℝ, 0 ≤ t → SpectralMeanZero (u t).val) :
    Nonempty (GlobalStrongCoefficientNSE ν a ha) := by
  refine ⟨{
    state := u
    stateH2 := u2
    derivativeH0 := v
    continuous := hu
    initial := hinit
    local_H1 := fun T _ => continuousOn_forward_memLp u hu T ⊤
    local_H2 := fun T _ => continuousOn_forward_memLp u2 hu2 T 2
    local_derivative := fun T _ => continuousOn_forward_memLp v hv T 2
    H2_agreement := ?_
    derivative_integrable := ?_
    time_integral := hint
    equation := ?_
    reality := hreal
    solenoidal := hsol
    mean_zero := hzero
  }⟩
  · intro T hT
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact h2 t ht.1
  · intro T hT
    exact (hv.mono (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
  · intro T hT
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact heq t ht.1

end

end SingularClosure
