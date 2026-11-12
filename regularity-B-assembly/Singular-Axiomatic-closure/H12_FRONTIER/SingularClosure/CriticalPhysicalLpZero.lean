import SingularClosure.Contracts

/-! Abstract normed-space zero identities for the physical L2 seminorm.
Keeping the codomain abstract avoids expanding bundled operator-space
instances when constructing constant smooth approximations. -/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SingularClosure

theorem critical_physical_eLpNorm_zero
    {E : Type*} [NormedAddCommGroup E] :
    eLpNorm (fun _ : Vec => (0 : E)) 2 (volume.restrict unitCube) = 0 :=
  eLpNorm_zero'

theorem critical_physical_self_sub_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] (f : Vec → E) :
    Tendsto (fun _ : ℕ => eLpNorm (f - f) 2 (volume.restrict unitCube))
      atTop (𝓝 0) := by
  have hz : f - f = (fun _ : Vec => (0 : E)) := by
    funext x
    exact sub_self _
  simpa only [hz, critical_physical_eLpNorm_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

end SingularClosure
