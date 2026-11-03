import HVR_Zeta_CorrectionIdentity
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section

/-!
Candidate normalized log-derivative residue at the pole of the actual zeta
function. This uses Mathlib's near-pole zeta asymptotic; it proves no boundary
nonvanishing or PNT. The imported theorem's transitive dependencies and the
pinned cache availability must be independently checked. No Lean execution
has been performed on this source.
-/
namespace HVRZetaPoleResidue

open Filter Asymptotics
open scoped Topology

/-- The bounded regular part of the logarithmic derivative has its actual
finite limit at the pole, along the punctured complex neighborhood. -/
theorem logDerivative_regular_part_tendsto :
    Tendsto (fun s : ℂ => deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹)
      (𝓝[≠] (1 : ℂ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hz : Tendsto
      (fun s : ℂ => deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ -
        (Real.eulerMascheroniConstant : ℂ))
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) :=
    (isLittleO_one_iff ℂ).mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  have ha := hz.add_const (Real.eulerMascheroniConstant : ℂ)
  simpa only [sub_add_cancel, zero_add] using ha

/-- The normalized negative logarithmic derivative has residue one at s=1. -/
theorem normalized_zeta_logDerivative_tendsto_one :
    Tendsto (fun s : ℂ => (s - 1) * (-deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using hid.sub_const (1 : ℂ)
  have hm := hs.mul logDerivative_regular_part_tendsto
  have hh : Tendsto
      (fun s : ℂ => 1 - (s - 1) *
        (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹))
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa only [zero_mul, sub_zero] using tendsto_const_nhds.sub hm
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s ≠ (1 : ℂ) := by simpa using hs
  have hcancel : (s - 1) * (s - 1)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hne)
  rw [mul_add, hcancel]
  ring

end HVRZetaPoleResidue
