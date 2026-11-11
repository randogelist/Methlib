import SingularClosure.FourierLimitEquation
import SingularClosure.FourierProduct

/-!
# Actual transport coefficients along a uniform Galerkin limit

The finite Galerkin transport equals the genuine divergence convolution by
its actual support and solenoidality. The fixed-frequency bounded bilinear
map then transfers compact-time uniform H0 convergence to uniform convergence
of every transport coefficient.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology

namespace SingularClosure

noncomputable section

/-- Exact equality of the finite transport and the full physical convolution. -/
theorem GalerkinSolution.coefficientTransport_eq_fullTransport
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) :
    coefficientTransport N (g.coeff t) = fullTransportCoefficients (g.sobolevState 0 t) := by
  have hc := g.sobolevState_coeff 0 ht
  have hs : ∀ p : Frequency, p ∉ cutoffModes N → ∀ j : Fin 3,
      (g.sobolevState 0 t).val p j = 0 := by
    rw [hc]
    exact g.mode_support t ht
  have hsol : SpectralSolenoidal (g.sobolevState 0 t).val := by
    rw [hc]
    exact g.solenoidal t ht
  funext k i
  have h := coefficientTransport_eq_divergenceTransport N
    (g.sobolevState 0 t) hs hsol k i
  simpa only [hc, fullTransportCoefficients] using h

theorem fullTransportCoefficients_continuous (k : Frequency) (i : Fin 3) :
    Continuous (fun c : TorusSobolev 0 => fullTransportCoefficients c k i) :=
  (divergenceTransportCoefficient_continuous k i).comp
    (continuous_id.prodMk continuous_id)

/-- Compact-time uniform H0 convergence preserves every full transport mode. -/
theorem fullTransportCoefficients_tendstoUniformlyOn
    (k : Frequency) (i : Fin 3) (T : ℝ)
    {F : ℕ → ℝ → TorusSobolev 0} {u : ℝ → TorusSobolev 0}
    (hF : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn F u atTop (Icc (0 : ℝ) T)) :
    TendstoUniformlyOn (fun n t => fullTransportCoefficients (F n t) k i)
      (fun t => fullTransportCoefficients (u t) k i) atTop (Icc (0 : ℝ) T) := by
  letI : CompactSpace (Icc (0 : ℝ) T) := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : ℕ → C(Icc (0 : ℝ) T, TorusSobolev 0) := fun n =>
    ⟨fun t => F n t.val, continuousOn_iff_continuous_restrict.mp (hF n)⟩
  let v : C(Icc (0 : ℝ) T, TorusSobolev 0) :=
    ⟨fun t => u t.val, continuousOn_iff_continuous_restrict.mp hu⟩
  let R : C(TorusSobolev 0, ℂ) := ⟨fun c => fullTransportCoefficients c k i,
    fullTransportCoefficients_continuous k i⟩
  have hf : Tendsto f atTop (𝓝 v) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hconv
  have hr := ((ContinuousMap.continuous_postcomp R).tendsto v).comp hf
  have hr' := ContinuousMap.tendsto_iff_tendstoUniformly.mp hr
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hr'

/-- The literal Galerkin transport converges uniformly to the actual limiting
convolution; no transport-agreement certificate is an additional premise. -/
theorem galerkinLimit_transport_tendstoUniformlyOn
    (ν : ℝ) (a : Field) (φ : ℕ → ℕ)
    (g : ∀ n : ℕ, GalerkinSolution ν a (φ n + 1))
    (T : ℝ) (u : ℝ → TorusSobolev 0)
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T)) (k : Frequency) (i : Fin 3) :
    TendstoUniformlyOn (fun n t => coefficientTransport (φ n + 1) ((g n).coeff t) k i)
      (fun t => fullTransportCoefficients (u t) k i) atTop (Icc (0 : ℝ) T) := by
  have hF (n : ℕ) : ContinuousOn (fun t => (g n).sobolevState 0 t) (Icc (0 : ℝ) T) :=
    ((g n).sobolevState_continuousOn 0).mono (fun t ht => ht.1)
  apply (fullTransportCoefficients_tendstoUniformlyOn k i T hF hu hconv).congr
  apply Filter.Eventually.of_forall
  intro n t ht
  exact congrFun (congrFun
    ((g n).coefficientTransport_eq_fullTransport t ht.1).symm k) i

end

end SingularClosure
