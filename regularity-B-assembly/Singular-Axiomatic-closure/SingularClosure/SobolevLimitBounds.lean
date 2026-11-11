import SingularClosure.TorusSobolev

/-! Pointwise limits and strong convergence in the actual Fourier Sobolev
spaces. The norm bound is lower semicontinuity of the explicit weighted lp
representation; strong convergence uses the proved compact Sobolev inclusion. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators

namespace SingularClosure

noncomputable section

/-- Evaluation of an actual Fourier coefficient in any Sobolev order. -/
def torusSobolevCoeff (s : ℕ) (k : Frequency) (i : Fin 3) : TorusSobolev s →L[ℂ] ℂ :=
  ((torusSobolevWeight k : ℂ) ^ s)⁻¹ •
    ((lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 (k, i)).comp
      (torusSobolevRepr s).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem torusSobolevCoeff_apply (s : ℕ) (k : Frequency) (i : Fin 3)
    (c : TorusSobolev s) : torusSobolevCoeff s k i c = c.val k i := by
  change ((torusSobolevWeight k : ℂ) ^ s)⁻¹ *
    ((torusSobolevWeight k : ℂ) ^ s * c.val k i) = c.val k i
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero s (torusSobolevWeight_ne_zero k)), one_mul]

theorem torusSobolevCoeff_continuous (s : ℕ) (k : Frequency) (i : Fin 3) :
    Continuous (fun c : TorusSobolev s => c.val k i) := by
  simpa only [torusSobolevCoeff_apply] using (torusSobolevCoeff s k i).continuous

theorem torusSobolev_weighted_coeff_tendsto
    {α : Type*} {l : Filter α} (s : ℕ) (u : α → TorusSobolev s) (c : FourierCoeff)
    (hcoeff : ∀ k i, Tendsto (fun n => (u n).val k i) l (𝓝 (c k i))) :
    Tendsto (fun n => (torusSobolevRepr s (u n) : FourierIndex → ℂ)) l
      (𝓝 (sobolevWeightedCoeff s c)) := by
  apply tendsto_pi_nhds.mpr
  intro ki
  exact (hcoeff ki.1 ki.2).const_mul ((torusSobolevWeight ki.1 : ℂ) ^ s)

/-- Uniform actual Hs bounds survive pointwise Fourier coefficient limits.
No membership or finite-energy certificate for the limit is assumed. -/
theorem torusSobolev_limit_mem_and_norm_le
    {α : Type*} {l : Filter α} [l.NeBot]
    (s : ℕ) (u : α → TorusSobolev s) (c : FourierCoeff) (B : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ B)
    (hcoeff : ∀ k i, Tendsto (fun n => (u n).val k i) l (𝓝 (c k i))) :
    ∃ hc : Memℓp (sobolevWeightedCoeff s c) 2,
      ‖(⟨c, hc⟩ : TorusSobolev s)‖ ≤ B := by
  have hrepr : ∀ n, ‖torusSobolevRepr s (u n)‖ ≤ B := by
    intro n
    simpa only [(torusSobolevRepr s).norm_map] using hbound n
  have hbounded : Bornology.IsBounded (range (fun n => torusSobolevRepr s (u n))) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hrepr n
  have hconv := torusSobolev_weighted_coeff_tendsto s u c hcoeff
  have hmem : Memℓp (sobolevWeightedCoeff s c) 2 :=
    lp.memℓp_of_tendsto hbounded hconv
  refine ⟨hmem, ?_⟩
  change ‖(⟨sobolevWeightedCoeff s c, hmem⟩ : FourierVectorSequence)‖ ≤ B
  exact lp.norm_le_of_tendsto (Filter.Eventually.of_forall hrepr) hconv

/-- One higher uniform Sobolev bound upgrades coefficient convergence to strong
Hs convergence along an arbitrary filter. -/
theorem torusSobolevInclusion_tendsto_of_coeff_tendsto
    {α : Type*} {l : Filter α} (s : ℕ)
    (u : α → TorusSobolev (s + 1)) (v : TorusSobolev s) (B : ℝ)
    (hbound : ∀ᶠ n in l, ‖u n‖ ≤ B)
    (hcoeff : ∀ k i, Tendsto (fun n => (u n).val k i) l (𝓝 (v.val k i))) :
    Tendsto (fun n => torusSobolevInclusion s (u n)) l (𝓝 v) := by
  let K : Set (TorusSobolev s) :=
    closure ((torusSobolevInclusion s) '' Metric.closedBall (0 : TorusSobolev (s + 1)) B)
  have hK : IsCompact K :=
    (torusSobolevInclusion_compact s).isCompact_closure_image_closedBall B
  have hmem : ∀ᶠ n in l, torusSobolevInclusion s (u n) ∈ K := by
    filter_upwards [hbound] with n hn
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  apply hK.tendsto_nhds_of_unique_mapClusterPt hmem
  intro z hz hcluster
  apply Subtype.ext
  funext k i
  have heval : MapClusterPt (z.val k i) l
      (fun n => (torusSobolevInclusion s (u n)).val k i) :=
    hcluster.continuousAt_comp (torusSobolevCoeff_continuous s k i).continuousAt
  have hpoint : Tendsto
      (fun n => (torusSobolevInclusion s (u n)).val k i) l (𝓝 (v.val k i)) := by
    simpa only [torusSobolevInclusion_coeff] using hcoeff k i
  exact eq_of_nhds_neBot (heval.clusterPt.mono hpoint)

/-- Membership, the inherited bound, and strong convergence are obtained
together from the actual one-higher-order coefficient bounds. -/
theorem torusSobolev_limit_of_bounded_higher_order
    {α : Type*} {l : Filter α} [l.NeBot]
    (s : ℕ) (u : α → TorusSobolev (s + 1)) (c : FourierCoeff) (B : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ B)
    (hcoeff : ∀ k i, Tendsto (fun n => (u n).val k i) l (𝓝 (c k i))) :
    ∃ v : TorusSobolev (s + 1), v.val = c ∧ ‖v‖ ≤ B ∧
      Tendsto (fun n => torusSobolevInclusion s (u n)) l
        (𝓝 (torusSobolevInclusion s v)) := by
  obtain ⟨hc, hnorm⟩ := torusSobolev_limit_mem_and_norm_le (s + 1) u c B hbound hcoeff
  let v : TorusSobolev (s + 1) := ⟨c, hc⟩
  refine ⟨v, rfl, hnorm, ?_⟩
  apply torusSobolevInclusion_tendsto_of_coeff_tendsto s u
    (torusSobolevInclusion s v) B (Filter.Eventually.of_forall hbound)
  intro k i
  simpa only [torusSobolevInclusion_coeff] using hcoeff k i

end

end SingularClosure
