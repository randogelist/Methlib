import SingularClosure.GlobalSobolevCurve
import SingularClosure.SobolevLimitInitial
import SingularClosure.SmoothDatumSobolev

/-!
# Actual initial data and Fourier constraints of the global Sobolev limits

The adjacent inclusion identities identify the raw coefficients at every order.
The proved H0 initial-trace theorem therefore determines the initial state in
every Sobolev space. H0 coefficient continuity passes the actual Galerkin
reality, solenoidality and zero-mode identities to the common global limit.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace SingularClosure

noncomputable section

theorem globalSobolevCurves_coeff_eq_H0
    (U : ∀ r : ℕ, ℝ → TorusSobolev r)
    (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      torusSobolevInclusion r (U (r + 1) t) = U r t)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (U r t).val = (U 0 t).val := by
  induction r with
  | zero => rfl
  | succ r ih =>
      calc
        (U (r + 1) t).val = (torusSobolevInclusion r (U (r + 1) t)).val :=
          (torusSobolevInclusion_coeff r (U (r + 1) t)).symm
        _ = (U r t).val := congrArg (fun c : TorusSobolev r => c.val) (hinclusion r t ht)
        _ = (U 0 t).val := ih

theorem globalSobolevCurves_all_mem
    (U : ∀ r : ℕ, ℝ → TorusSobolev r)
    (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      torusSobolevInclusion r (U (r + 1) t) = U r t)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    Memℓp (sobolevWeightedCoeff r (U 0 t).val) 2 := by
  have hm : Memℓp (sobolevWeightedCoeff r (U r t).val) 2 := (U r t).property
  rwa [globalSobolevCurves_coeff_eq_H0 U hinclusion r t ht] at hm

theorem globalSobolevCurves_initial
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (U : ∀ r : ℕ, ℝ → TorusSobolev r) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hcontinuous : ContinuousOn (U 0) (Ici 0))
    (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      torusSobolevInclusion r (U (r + 1) t) = U r t)
    (hconv : TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      (U 0) atTop (Icc (0 : ℝ) 1))
    (r : ℕ) : U r 0 = smoothDatumSobolev r a ha.smooth ha.periodic := by
  let u0 : C(Icc (0 : ℝ) 1, TorusSobolev 0) :=
    { toFun := fun t => U 0 t.val
      continuous_toFun := continuousOn_iff_continuous_restrict.mp
        (hcontinuous.mono (fun t ht => ht.1)) }
  have hconv0 : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) 1) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
      u0 atTop := tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hconv
  have h0 : (U 0 0).val = datumFourierCoeff a :=
    canonicalSobolevLimit_initial_coeff ν hν a ha 1 (by norm_num) u0 φ hφ hconv0
  apply Subtype.ext
  change (U r 0).val = datumFourierCoeff a
  rw [globalSobolevCurves_coeff_eq_H0 U hinclusion r 0 le_rfl, h0]

theorem globalSobolevCurves_constraints
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (U : ∀ r : ℕ, ℝ → TorusSobolev r) (φ : ℕ → ℕ)
    (hinclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
      torusSobolevInclusion r (U (r + 1) t) = U r t)
    (hconv : ∀ T : ℝ, TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      (U 0) atTop (Icc (0 : ℝ) T))
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    SpectralReality (U r t).val ∧ SpectralSolenoidal (U r t).val ∧
      SpectralMeanZero (U r t).val := by
  rw [globalSobolevCurves_coeff_eq_H0 U hinclusion r t ht]
  have hlim := (hconv t).tendsto_at (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩)
  refine ⟨torusSobolevH0_reality_of_tendsto hlim ?_,
    torusSobolevH0_solenoidal_of_tendsto hlim ?_,
    torusSobolevH0_zero_mode_of_tendsto hlim ?_⟩
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_reality 0 t ht
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_solenoidal 0 t ht
  · exact Filter.Eventually.of_forall fun n =>
      (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_zero_mode 0 t ht

/-- The common actual global Sobolev curves retain the physical initial datum
and all three Fourier constraints at every nonnegative time and Sobolev order. -/
theorem AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_TRACE (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ U : ∀ r : ℕ, ℝ → TorusSobolev r, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ r, ContinuousOn (U r) (Ici 0)) ∧
      (∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        torusSobolevInclusion r (U (r + 1) t) = U r t) ∧
      (∀ (T : ℝ) (r : ℕ), TendstoUniformlyOn
        (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState r t)
        (U r) atTop (Icc (0 : ℝ) T)) ∧
      (∀ r, U r 0 = smoothDatumSobolev r a ha.smooth ha.periodic) ∧
      ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
        SpectralReality (U r t).val ∧ SpectralSolenoidal (U r t).val ∧
          SpectralMeanZero (U r t).val := by
  obtain ⟨U, φ, hφ, hcontinuous, hinclusion, hconv⟩ :=
    AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_CURVES hAX6 ν hν a ha
  exact ⟨U, φ, hφ, hcontinuous, hinclusion, hconv,
    globalSobolevCurves_initial ν hν a ha U φ hφ (hcontinuous 0) hinclusion (hconv 1 0),
    globalSobolevCurves_constraints ν hν a ha U φ hinclusion (fun T => hconv T 0)⟩

end

end SingularClosure
