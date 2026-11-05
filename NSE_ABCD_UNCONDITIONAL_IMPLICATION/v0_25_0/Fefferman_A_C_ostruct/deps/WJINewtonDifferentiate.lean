import WJINewtonKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace CondFeffA

open Fefferman.ConcreteReal MeasureTheory Set Metric Filter
open scoped Convolution Topology
noncomputable section

theorem newtonKernel_locallyIntegrable : LocallyIntegrable newtonKernel volume := by
  have hd : Module.finrank ℝ RSpace = 3 := Module.finrank_fin_fun ℝ
  apply locallyIntegrable_of_norm_le_rpow (E := RSpace) (μ := volume)
    (f := newtonKernel) (C := (1 : ℝ)) (α := (1 : ℝ))
    (by rw [hd]; decide) (by rw [hd]; norm_num)
  · exact Eventually.of_forall fun z => by
      simpa only [one_mul, Real.rpow_neg_one, pow_one] using newtonKernel_majorized z
  · exact newtonKernel_measurable.aestronglyMeasurable

theorem newtonPotential_eq_convolution (g : RSpace → ℝ) :
    newtonPotential g = g ⋆ newtonKernel := by
  funext x
  simp only [newtonPotential, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, div_eq_mul_inv, newtonKernel]

theorem newtonPotential_compact_contDiff {g : RSpace → ℝ} {k : ℕ∞}
    (hc : HasCompactSupport g) (hs : ContDiff ℝ k g) :
    ContDiff ℝ k (newtonPotential g) := by
  rw [newtonPotential_eq_convolution]
  exact hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hs
    newtonKernel_locallyIntegrable

/-- Compact C¹ sources allow the derivative to fall on the source. -/
theorem newtonPotential_compact_hasFDerivAt {g : RSpace → ℝ}
    (hc : HasCompactSupport g) (hs : ContDiff ℝ 1 g) (x : RSpace) :
    HasFDerivAt (newtonPotential g)
      (∫ y, newtonKernel (x-y) • fderiv ℝ g y) x := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have he : convolution (fderiv ℝ g) newtonKernel (L.precompL RSpace) volume x =
      ∫ y, newtonKernel (x-y) • fderiv ℝ g y := by
    unfold MeasureTheory.convolution
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    change (L.precompL RSpace) (fderiv ℝ g y) (newtonKernel (x-y)) =
      newtonKernel (x-y) • fderiv ℝ g y
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.precompL_apply]
    change fderiv ℝ g y v * newtonKernel (x-y) = newtonKernel (x-y) * fderiv ℝ g y v
    exact mul_comm _ _
  have hd := hc.hasFDerivAt_convolution_left L hs newtonKernel_locallyIntegrable x
  rw [he] at hd
  rw [newtonPotential_eq_convolution]
  exact hd

private abbrev NewtonCovector := RSpace →L[ℝ] ℝ

private def covectorPotential (J : RSpace → NewtonCovector) (x : RSpace) : NewtonCovector :=
  ∫ y, newtonKernel (x-y) • J y

private theorem covector_integrable {J : RSpace → NewtonCovector} (hJ : Integrable J)
    {B : ℝ} (hB : ∀ y, ‖J y‖ ≤ B) (x : RSpace) :
    Integrable (fun y => newtonKernel (x-y) • J y) := by
  have hb (y : RSpace) : ‖‖J y‖‖ ≤ B := by simpa only [norm_norm] using hB y
  have hi := integrable_newton_majorized (k := 1) (by decide) newtonKernel_measurable
    newtonKernel_majorized hJ.norm hb x
  apply hi.norm.mono'
  · exact ((newtonKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      : AEStronglyMeasurable (fun y : RSpace => newtonKernel (x-y)) volume).smul
      hJ.aestronglyMeasurable
  · apply Eventually.of_forall
    intro y
    simpa only [norm_smul, norm_mul, norm_norm, mul_comm] using
      (le_refl (‖newtonKernel (x-y)‖ * ‖J y‖))

theorem newtonPotential_compact_partial {g : RSpace → ℝ}
    (hc : HasCompactSupport g) (hs : ContDiff ℝ 1 g) (i : Fin 3) (x : RSpace) :
    spatialDerivative i (newtonPotential g) x =
      newtonPotential (spatialDerivative i g) x := by
  let φ := fun y : RSpace => newtonKernel (x-y) • fderiv ℝ g y
  have hd : Continuous (fderiv ℝ g) := hs.continuous_fderiv one_ne_zero
  have hcompact : HasCompactSupport (fderiv ℝ g) := hc.fderiv ℝ
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuous hd
  have hi : Integrable φ :=
    covector_integrable (J := fderiv ℝ g) (B := M)
      (hd.integrable_of_hasCompactSupport hcompact) hM x
  change (fderiv ℝ (newtonPotential g) x) (basisDirection i) = _
  rw [(newtonPotential_compact_hasFDerivAt hc hs x).fderiv]
  change (∫ y, φ y) (basisDirection i) = _
  rw [ContinuousLinearMap.integral_apply hi (basisDirection i)]
  unfold newtonPotential
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change newtonKernel (x-y) * fderiv ℝ g y (basisDirection i) =
    fderiv ℝ g y (basisDirection i) / (4 * Real.pi * euclideanNorm3 (x-y))
  rw [newtonKernel, div_eq_mul_inv, mul_comm]

private theorem covector_bound {J : RSpace → NewtonCovector} (hJ : Integrable J)
    {B : ℝ} (hB : ∀ y, ‖J y‖ ≤ B) (x : RSpace) :
    ‖covectorPotential J x‖ ≤ B * newtonLocalMass 1 + ∫ y, ‖J y‖ := by
  have hk (z : RSpace) : 0 ≤ newtonKernel z :=
    inv_nonneg.mpr (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  calc
    _ ≤ ∫ y, ‖newtonKernel (x-y) • J y‖ := norm_integral_le_integral_norm _
    _ = newtonPotential (fun y => ‖J y‖) x := by
      unfold newtonPotential
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change ‖newtonKernel (x-y) • J y‖ = ‖J y‖ / (4 * Real.pi * euclideanNorm3 (x-y))
      rw [norm_smul, Real.norm_of_nonneg (hk _), newtonKernel, div_eq_mul_inv, mul_comm]
    _ ≤ ‖newtonPotential (fun y => ‖J y‖) x‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ _ := by
      have hb (y : RSpace) : ‖‖J y‖‖ ≤ B := by simpa only [norm_norm] using hB y
      simpa only [norm_norm] using newtonPotential_norm_le hJ.norm hb x

private theorem covector_tendstoUniformly {D : RSpace → NewtonCovector}
    {Dn : ℕ → RSpace → NewtonCovector} (hD : Integrable D) (hn : ∀ n, Integrable (Dn n))
    {B : ℝ} (hB : ∀ y, ‖D y‖ ≤ B)
    {C : ℕ → ℝ} (herr : ∀ n y, ‖Dn n y - D y‖ ≤ C n)
    (hC : Tendsto C atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ y, ‖Dn n y - D y‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => covectorPotential (Dn n)) (covectorPotential D) atTop := by
  have hb (n : ℕ) (y : RSpace) : ‖Dn n y‖ ≤ C n + B := calc
    _ = ‖(Dn n y - D y) + D y‖ := by rw [sub_add_cancel]
    _ ≤ ‖Dn n y - D y‖ + ‖D y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (herr n y) (hB y)
  have htot : Tendsto (fun n => C n * newtonLocalMass 1 + ∫ y, ‖Dn n y - D y‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using (hC.mul_const (newtonLocalMass 1)).add hL1
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [htot.eventually_lt_const hε] with n he
  intro x
  rw [dist_comm, dist_eq_norm]
  have hsub : covectorPotential (Dn n) x - covectorPotential D x =
      covectorPotential (fun y => Dn n y - D y) x := by
    unfold covectorPotential
    rw [← integral_sub (covector_integrable (hn n) (hb n) x) (covector_integrable hD hB x)]
    simp only [smul_sub]
  rw [hsub]
  exact (covector_bound ((hn n).sub hD) (herr n) x).trans_lt he

/-- Differentiation of the literal Newton integral from C¹ compact source
    approximants converging in value and first derivative in both L¹ and
    uniform norm. All convergence requirements concern the source alone. -/
theorem newtonPotential_hasFDerivAt_of_source_approx {g : RSpace → ℝ}
    {G : ℕ → RSpace → ℝ} (hc : ∀ n, HasCompactSupport (G n))
    (hs : ∀ n, ContDiff ℝ 1 (G n))
    (hg : Integrable g) (hdg : Integrable (fderiv ℝ g))
    {B Bd : ℝ} (hb : ∀ y, ‖g y‖ ≤ B) (hbd : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd)
    {C Cd : ℕ → ℝ} (herr : ∀ n y, ‖G n y - g y‖ ≤ C n)
    (herrd : ∀ n y, ‖fderiv ℝ (G n) y - fderiv ℝ g y‖ ≤ Cd n)
    (hC : Tendsto C atTop (𝓝 0)) (hCd : Tendsto Cd atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ y, ‖G n y - g y‖) atTop (𝓝 0))
    (hL1d : Tendsto (fun n => ∫ y, ‖fderiv ℝ (G n) y - fderiv ℝ g y‖) atTop (𝓝 0))
    (x : RSpace) :
    HasFDerivAt (newtonPotential g) (∫ y, newtonKernel (x-y) • fderiv ℝ g y) x := by
  have hG (n : ℕ) : Integrable (G n) :=
    (hs n).continuous.integrable_of_hasCompactSupport (hc n)
  have hGd (n : ℕ) : Integrable (fderiv ℝ (G n)) :=
    ((hs n).continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport ((hc n).fderiv ℝ)
  have hi := newtonPotential_tendstoUniformly hg hG hb herr hC hL1
  have hd := covector_tendstoUniformly hdg hGd hbd herrd hCd hL1d
  exact hasFDerivAt_of_tendstoUniformly hd
    (fun n y => newtonPotential_compact_hasFDerivAt (hc n) (hs n) y) hi.tendsto_at x

end
end CondFeffA
