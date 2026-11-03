import HVR_Zeta_BoundaryFactor
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Filter
open scoped Topology

/-!
A generic finite-order logarithmic-derivative residue for a locally
factored analytic germ. The factorization and the nonvanishing of the
analytic factor are explicit hypotheses. This source contains no zeta
boundary nonvanishing or PNT input. External compilation and axiom audit are
required; no Lean execution was performed locally.
-/
namespace HVRAnalyticResidue

/-- A locally nonvanishing analytic factor has a continuous log derivative. -/
theorem logDeriv_continuousAt_of_analytic
    (g : ℂ → ℂ) (s : ℂ) (hg : AnalyticAt ℂ g s) (hgn : g s ≠ 0) :
    ContinuousAt (logDeriv g) s := by
  change ContinuousAt (fun z : ℂ => deriv g z / g z) s
  exact hg.deriv.continuousAt.div hg.continuousAt hgn

/-- If f has a finite-order factorization at s, its normalized negative
logarithmic derivative tends to minus the order in the punctured plane. -/
theorem normalized_neg_logDeriv_tendsto
    (f g : ℂ → ℂ) (s : ℂ) (m : ℕ)
    (hg : AnalyticAt ℂ g s) (hgn : g s ≠ 0)
    (hfac : f =ᶠ[𝓝 s] fun z : ℂ => (z - s) ^ m * g z) :
    Tendsto (fun z : ℂ => (z - s) * (-deriv f z / f z))
      (𝓝[≠] s) (𝓝 (-(m : ℂ))) := by
  have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] s) (𝓝 s) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun z : ℂ => z - s) (𝓝[≠] s) (𝓝 0) := by
    simpa only [sub_self] using hid.sub_const s
  have hlog : Tendsto (logDeriv g) (𝓝[≠] s) (𝓝 (logDeriv g s)) :=
    (logDeriv_continuousAt_of_analytic g s hg hgn).tendsto.mono_left
      nhdsWithin_le_nhds
  have hprod := hsub.mul hlog
  have hlimit : Tendsto (fun z : ℂ => -((m : ℂ) + (z - s) * logDeriv g z))
      (𝓝[≠] s) (𝓝 (-(m : ℂ))) := by
    have hc : Tendsto (fun _ : ℂ => (m : ℂ)) (𝓝[≠] s) (𝓝 (m : ℂ)) :=
      tendsto_const_nhds
    simpa only [zero_mul, add_zero] using (hc.add hprod).neg
  apply hlimit.congr'
  have hcongr : logDeriv f =ᶠ[𝓝[≠] s]
      logDeriv (fun z : ℂ => (z - s) ^ m * g z) :=
    (logDeriv_congr_nhds hfac).filter_mono nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in 𝓝[≠] s, g z ≠ 0 :=
    (hg.continuousAt.eventually_ne hgn).filter_mono nhdsWithin_le_nhds
  have hanalytic : ∀ᶠ z in 𝓝[≠] s, AnalyticAt ℂ g z :=
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  filter_upwards [hcongr, hnear, hanalytic, self_mem_nhdsWithin] with z hcon hz hg_at hne
  have hzs : z ≠ s := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
  have hsubne : z - s ≠ 0 := sub_ne_zero.mpr hzs
  have hbase : DifferentiableAt ℂ (fun w : ℂ => w - s) z := by fun_prop
  have hbase_deriv : deriv (fun w : ℂ => w - s) z = 1 := by
    simpa using ((hasDerivAt_id z).sub_const s).deriv
  have hbase_log : logDeriv (fun w : ℂ => w - s) z = 1 / (z - s) := by
    rw [logDeriv_apply, hbase_deriv]
  have hmul : logDeriv (fun w : ℂ => (w - s) ^ m * g w) z =
      logDeriv (fun w : ℂ => (w - s) ^ m) z + logDeriv g z :=
    logDeriv_fun_mul z (pow_ne_zero m hsubne) hz (hbase.pow m) hg_at.differentiableAt
  rw [neg_div, ← logDeriv_apply f z, hcon, hmul, logDeriv_fun_pow hbase m, hbase_log]
  field_simp [hsubne]
  <;> ring

end HVRAnalyticResidue
