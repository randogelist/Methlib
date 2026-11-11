import SingularClosure.SmoothEvaluation
import SingularClosure.CanonicalRhsSobolev

/-!
# The literal physical time derivative of the smooth Fourier realization

Physical evaluation is a proved bounded real linear map on H4. Composition
with the actual Sobolev derivative therefore differentiates the literal
pointwise Fourier synthesis, including at the initial endpoint. No temporal
termwise differentiation or physical derivative identification is assumed.
-/

set_option autoImplicit false

open Set

namespace SingularClosure

noncomputable section

theorem smoothFourierSynthesis_hasDerivWithinAt_H4
    (u : ℝ → TorusSobolev 4) (r : TorusSobolev 4) (t : ℝ) (x : Vec)
    (hu : HasDerivWithinAt u r (Ici 0) t) :
    HasDerivWithinAt (fun z => smoothFourierSynthesis (u z).val x)
      (smoothFourierSynthesis r.val x) (Ici 0) t := by
  have h := (sobolevPhysicalEvaluation4 x).hasFDerivAt.comp_hasDerivWithinAt t hu
  simpa only [Function.comp_def, sobolevPhysicalEvaluation4,
    sobolevPhysicalEvaluation_apply] using! h

/-- Compatible actual H4 representatives identify the literal pointwise derivative. -/
theorem physicalTimeDerivative_of_H4_curve
    (u0 : ℝ → TorusSobolev 0) (u4 : ℝ → TorusSobolev 4)
    (r0 : ℝ → TorusSobolev 0) (r4 : ℝ → TorusSobolev 4)
    (hu : ∀ t : ℝ, 0 ≤ t → (u4 t).val = (u0 t).val)
    (hr : ∀ t : ℝ, 0 ≤ t → (r4 t).val = (r0 t).val)
    (hd : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u4 (r4 t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative (fun z => smoothFourierSynthesis (u0 z).val) t =
      smoothFourierSynthesis (r0 t).val := by
  funext x
  have h := smoothFourierSynthesis_hasDerivWithinAt_H4 u4 (r4 t) t x (hd t ht)
  have h' : HasDerivWithinAt (fun z => smoothFourierSynthesis (u0 z).val x)
      (smoothFourierSynthesis (r4 t).val x) (Ici 0) t := by
    apply h.congr_of_mem _ ht
    intro z hz
    rw [hu z hz]
  rw [hr t ht] at h'
  exact h'.derivWithin ((uniqueDiffOn_Ici 0) t ht)

/-- The physical derivative of the actual canonical limit is the smooth
realization of its already constructed full Fourier RHS. -/
theorem canonicalLimit_physical_timeDerivative
    (hAX6 : AX6Statement) (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (u : ℝ → TorusSobolev 0) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      u Filter.atTop (Icc (0 : ℝ) T))
    (hu : ContinuousOn u (Ici 0)) (u4 : ℝ → TorusSobolev 4)
    (hu4 : ∀ t : ℝ, 0 ≤ t → (u4 t).val = (u t).val)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative (fun z => smoothFourierSynthesis (u z).val) t =
      smoothFourierSynthesis (fullFourierRhs ν (u t)) := by
  let R := canonicalLimitRhsSobolev hAX6 ν hν a ha u φ hφ hconv
  have hderiv (z : ℝ) (hz : 0 ≤ z) : HasDerivWithinAt u4 (R 4 z) (Ici 0) z :=
    canonicalLimitRhsSobolev_hasDerivWithinAt_order
      hAX6 ν hν a ha u φ hφ hconv hu 4 u4 hu4 z hz
  have hr (z : ℝ) (hz : 0 ≤ z) : (R 4 z).val = (R 0 z).val := by
    rw [canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv 4 z hz,
      canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv 0 z hz]
  rw [physicalTimeDerivative_of_H4_curve u u4 (R 0) (R 4) hu4 hr hderiv t ht]
  rw [canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha u φ hφ hconv 0 t ht]

end

end SingularClosure
