import Mathlib

/-!
# QFA finite-interval energy-product budget

Source baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Source toolchain: Lean 4.33.0.

Status: prepared Lean proof candidates; no local Lean execution, external
compiler result, or theorem-level axiom-audit result is asserted.

The endpoint is scalar. The actual whole-space Leray--Hopf trajectory must
separately supply `D` interval integrability, `E` a.e. measurability, the sign
hypotheses, and the energy-envelope inequality. No continuity or derivative
hypothesis is imposed on `E`. No Navier--Stokes existence, regularity, or
uniqueness assertion is included among the conclusions of this module.

The EP references refer to version 1.2 of
`QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER.txt`, section [04].
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace QFA.Energy

/-- The absolutely continuous envelope associated with the dissipation profile.
The parameter `M` specializes to the initial spatial L2 norm. -/
def envelope (M ν : ℝ) (D : ℝ → ℝ) (t : ℝ) : ℝ :=
  M ^ 2 - 2 * ν * (∫ r in (0 : ℝ)..t, D r)

@[simp]
theorem envelope_zero (M ν : ℝ) (D : ℝ → ℝ) :
    envelope M ν D 0 = M ^ 2 := by
  simp [envelope]

/-- D04.02: interval integrability of `D` suffices for absolute continuity of
the envelope. The orientation of the interval is immaterial to this lemma. -/
theorem envelope_absolutelyContinuousOnInterval
    {M ν R : ℝ} {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (0 : ℝ) R) :
    AbsolutelyContinuousOnInterval (envelope M ν D) 0 R := by
  -- EP013: the primitive of an interval-integrable real function is AC.
  have hA : AbsolutelyContinuousOnInterval
      (fun t : ℝ => ∫ r in (0 : ℝ)..t, D r) 0 R :=
    hD.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  -- EP014: applied only to the constant term, not to the weak profile.
  have hC : AbsolutelyContinuousOnInterval (fun _ : ℝ => M ^ 2) 0 R := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact contDiffOn_const
  -- EP015 and EP016: scaling and subtraction preserve AC.
  change AbsolutelyContinuousOnInterval
    ((fun _ : ℝ => M ^ 2) -
      (fun t : ℝ => 2 * ν * (∫ r in (0 : ℝ)..t, D r))) 0 R
  exact hC.sub (AbsolutelyContinuousOnInterval.const_mul (2 * ν) hA)

/-- D04.03: only the envelope is differentiated, and only a.e. on the interval. -/
theorem envelope_hasDerivAt_ae
    {M ν R : ℝ} {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (0 : ℝ) R) :
    ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) R →
      HasDerivAt (envelope M ν D) (-(2 * ν * D t)) t := by
  -- EP017: local Lebesgue differentiation for the integral primitive.
  filter_upwards [hD.ae_hasDerivAt_integral] with t ht
  intro htmem
  have hA := ht htmem (0 : ℝ) (by simp)
  -- EP018 and EP019: scale the primitive and subtract from the constant.
  change HasDerivAt
    (fun x : ℝ => M ^ 2 - 2 * ν * (∫ r in (0 : ℝ)..x, D r))
    (-(2 * ν * D t)) t
  exact HasDerivAt.const_sub (M ^ 2) (HasDerivAt.const_mul (2 * ν) hA)

/-- D04.04: the continuous envelope times the integrable dissipation is
integrable, before any comparison with the weak energy profile is made. -/
theorem envelope_product_intervalIntegrable
    {M ν R : ℝ} {D : ℝ → ℝ}
    (hD : IntervalIntegrable D volume (0 : ℝ) R) :
    IntervalIntegrable (fun t => envelope M ν D t * D t) volume 0 R := by
  -- EP021 and EP022: AC implies continuity; continuous times L1 is L1.
  exact hD.continuousOn_mul
    (envelope_absolutelyContinuousOnInterval (M := M) (ν := ν) hD).continuousOn

/-- D04.05: exact square identity for the envelope. No sign assumption on `D`
or on `R` is required for this oriented-interval identity. -/
theorem envelope_product_integral
    {M ν R : ℝ} {D : ℝ → ℝ}
    (hν : ν ≠ 0)
    (hD : IntervalIntegrable D volume (0 : ℝ) R) :
    (∫ t in (0 : ℝ)..R, envelope M ν D t * D t) =
      (M ^ 4 - (envelope M ν D R) ^ 2) / (4 * ν) := by
  let F : ℝ → ℝ := envelope M ν D
  change (∫ t in (0 : ℝ)..R, F t * D t) =
    (M ^ 4 - (F R) ^ 2) / (4 * ν)
  have hF : AbsolutelyContinuousOnInterval F 0 R :=
    envelope_absolutelyContinuousOnInterval (M := M) (ν := ν) hD
  have hF0 : F 0 = M ^ 2 := by
    simp [F]
  -- EP024: AC product FTC with both factors equal to F.
  have hFTC :=
    AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hF hF
  have hderiv := envelope_hasDerivAt_ae (M := M) (ν := ν) hD
  have hrewrite :
      (∫ t in (0 : ℝ)..R, deriv F t * F t + F t * deriv F t) =
        -(4 * ν) * (∫ t in (0 : ℝ)..R, F t * D t) := by
    calc
      _ = ∫ t in (0 : ℝ)..R, -(4 * ν) * (F t * D t) := by
        -- EP025: replace the derivatives a.e., including the null endpoints.
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hderiv] with t ht
        intro htmem
        -- EP020: HasDerivAt determines the value of deriv.
        have hdt : deriv F t = -(2 * ν * D t) :=
          (ht (uIoc_subset_uIcc htmem)).deriv
        rw [hdt]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hrewrite, hF0] at hFTC
  apply (eq_div_iff (show 4 * ν ≠ 0 from
    mul_ne_zero (by norm_num) hν)).2
  nlinarith only [hFTC]

/-- D04.04--D04.06 isolated comparison stage.

`hidentity` is the displayed scalar envelope identity, not the desired product
budget. The main theorem `product_budget` below discharges it by the AC proof
`envelope_product_integral`. This helper does not assert a physical PDE fact.
-/
theorem product_budget_of_envelope_identity
    {E D F : ℝ → ℝ} {M ν R : ℝ}
    (hR : 0 ≤ R) (hν : 0 < ν)
    (hFD : IntervalIntegrable (fun t => F t * D t) volume (0 : ℝ) R)
    (hEm : AEStronglyMeasurable E (volume.restrict (Ioo (0 : ℝ) R)))
    (hDm : AEStronglyMeasurable D (volume.restrict (Ioo (0 : ℝ) R)))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), E t ≤ F t)
    (hidentity : (∫ t in (0 : ℝ)..R, F t * D t) =
      (M ^ 4 - (F R) ^ 2) / (4 * ν)) :
    Integrable (fun t => E t * D t) (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in (0 : ℝ)..R, E t * D t) ≤
        (M ^ 4 - (F R) ^ 2) / (4 * ν) ∧
      (∫ t in (0 : ℝ)..R, E t * D t) ≤ M ^ 4 / (4 * ν) := by
  -- EP011: a single null-endpoint measure equality transports all predicates.
  have hmeasure : volume.restrict (Ioo (0 : ℝ) R) =
      volume.restrict (Ioc (0 : ℝ) R) :=
    MeasureTheory.restrict_Ioo_eq_restrict_Ioc
  have hFDset : Integrable (fun t => F t * D t)
      (volume.restrict (Ioo (0 : ℝ) R)) := by
    rw [hmeasure]
    -- EP012: turn interval integrability into the half-open set form.
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hFD
  have hEDm : AEStronglyMeasurable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) R)) := by
    change AEStronglyMeasurable (E * D) (volume.restrict (Ioo (0 : ℝ) R))
    exact hEm.mul hDm
  have hEDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ E t * D t := by
    filter_upwards [hEnn, hDnn] with t hEt hDt
    exact mul_nonneg hEt hDt
  have hEDFD : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      E t * D t ≤ F t * D t := by
    filter_upwards [hEF, hDnn] with t hEFt hDt
    exact mul_le_mul_of_nonneg_right hEFt hDt
  -- EP023: establish ED integrability before applying integral monotonicity.
  have hED : Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) R)) :=
    hFDset.mono_nonneg hEDm hEDnn hEDFD
  have hcomparison : (∫ t in (0 : ℝ)..R, E t * D t) ≤
      ∫ t in (0 : ℝ)..R, F t * D t := by
    -- EP026 and EP027, followed by EP011 in the reverse direction.
    simpa only [intervalIntegral.integral_of_le hR, ← hmeasure] using
      (MeasureTheory.integral_mono_ae hED hFDset hEDFD)
  have hbudget : (∫ t in (0 : ℝ)..R, E t * D t) ≤
      (M ^ 4 - (F R) ^ 2) / (4 * ν) :=
    hcomparison.trans_eq hidentity
  have hupper : (M ^ 4 - (F R) ^ 2) / (4 * ν) ≤ M ^ 4 / (4 * ν) :=
    (div_le_div_iff_of_pos_right (show 0 < 4 * ν by positivity)).mpr
      (sub_le_self _ (sq_nonneg _))
  exact ⟨hED, hbudget, hbudget.trans hupper⟩

/-- Full scalar QFA product budget from the finite-interval energy envelope.

The hypotheses are exactly the scalar facts needed from a Leray--Hopf profile;
the envelope identity is proved within this module, not supplied as a premise.
The residual-square estimate and actual ED integrability are retained.
-/
theorem product_budget
    {E D : ℝ → ℝ} {M ν R : ℝ}
    (hR : 0 ≤ R) (hν : 0 < ν)
    (hD : IntervalIntegrable D volume (0 : ℝ) R)
    (hEm : AEStronglyMeasurable E (volume.restrict (Ioo (0 : ℝ) R)))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      E t ≤ envelope M ν D t) :
    Integrable (fun t => E t * D t) (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in (0 : ℝ)..R, E t * D t) ≤
        (M ^ 4 - (envelope M ν D R) ^ 2) / (4 * ν) ∧
      (∫ t in (0 : ℝ)..R, E t * D t) ≤ M ^ 4 / (4 * ν) := by
  have hDm : AEStronglyMeasurable D (volume.restrict (Ioo (0 : ℝ) R)) := by
    -- EP011, then the measurability field of interval integrability.
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact hD.aestronglyMeasurable
  exact product_budget_of_envelope_identity
    (E := E) (D := D) (F := envelope M ν D) (M := M) (ν := ν) (R := R)
    hR hν (envelope_product_intervalIntegrable (M := M) (ν := ν) hD)
    hEm hDm hDnn hEnn hEF
    (envelope_product_integral (M := M) (ν := ν) (ne_of_gt hν) hD)

/-- Open-interval interface for strict-average good-time extraction.
The measure is literally `volume.restrict (Ioo 0 R)`, so no periodic or
whole-space PDE carrier is built into this scalar conclusion. -/
theorem product_budget_Ioo
    {E D : ℝ → ℝ} {M ν R : ℝ}
    (hR : 0 ≤ R) (hν : 0 < ν)
    (hD : IntervalIntegrable D volume (0 : ℝ) R)
    (hEm : AEStronglyMeasurable E (volume.restrict (Ioo (0 : ℝ) R)))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      E t ≤ envelope M ν D t) :
    Integrable (fun t => E t * D t) (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in Ioo (0 : ℝ) R, E t * D t) ≤ M ^ 4 / (4 * ν) := by
  obtain ⟨hED, _, hbudget⟩ := product_budget
    (E := E) (D := D) (M := M) (ν := ν) (R := R) hR hν hD hEm hDnn hEnn hEF
  refine ⟨hED, ?_⟩
  -- EP027 and EP011: the strict-average source uses the open-set integral.
  simpa only [intervalIntegral.integral_of_le hR,
    ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc] using hbudget

end QFA.Energy
