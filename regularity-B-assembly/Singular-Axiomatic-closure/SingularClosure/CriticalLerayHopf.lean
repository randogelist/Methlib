import SingularClosure.CriticalH1Algebra
import SingularClosure.CriticalUniqueness

/-!
A physical Leray--Hopf class on the periodic cube.

The weak momentum equation uses all positive-time smooth solenoidal tests.
The spatial H1 class is the concrete physical closure of smooth periodic
fields.  Initial trace, weak L2 continuity, gradient time integrability and
both standard energy inequalities are explicit.  No relative-energy,
comparison, uniqueness, smoothing or existence property occurs in the class.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval

namespace SingularClosure

noncomputable section

abbrev CriticalPhysicalL2 := Lp Vec 2 (volume.restrict unitCube)

/-- The actual physical L2 equivalence class whenever the representative is
square integrable.  The zero branch is irrelevant on every stated energy class. -/
def criticalL2Representative {E : Type*} [NormedAddCommGroup E] (f : Vec → E) :
    Lp E 2 (volume.restrict unitCube) := by
  classical
  exact if hf : MemLp f 2 (volume.restrict unitCube) then hf.toLp f else 0

theorem criticalL2Representative_eq {E : Type*} [NormedAddCommGroup E]
    (f : Vec → E) (hf : MemLp f 2 (volume.restrict unitCube)) :
    criticalL2Representative f = hf.toLp f := by
  simp only [criticalL2Representative, dif_pos hf]

structure CriticalLerayHopf
    (ν : ℝ) (a₀ : CriticalPhysicalL2) (v : Velocity)
    (G : ℝ → Vec → (Vec →L[ℝ] Vec)) : Prop where
  momentum : CriticalIntegratedWeakMomentum ν v
  velocity_L2 : ∀ t : ℝ, 0 ≤ t → MemLp (v t) 2 (volume.restrict unitCube)
  velocity_energy_class : ∀ T : ℝ, 0 < T →
    MemLp (fun t => criticalL2Representative (v t)) ∞ (volume.restrict (Ioc (0 : ℝ) T))
  gradient_energy_class : ∀ T : ℝ, 0 < T →
    MemLp (fun t => criticalL2Representative (G t)) 2 (volume.restrict (Ioc (0 : ℝ) T))
  initial : v 0 =ᵐ[volume.restrict unitCube] (a₀ : Vec → Vec)
  weak_continuity : ∀ φ : Field, MemLp φ 2 (volume.restrict unitCube) →
    ContinuousOn (fun t => physicalFieldInner (v t) φ) (Ici 0)
  strong_trace : Tendsto
    (fun t => eLpNorm (v t - (a₀ : Vec → Vec)) 2 (volume.restrict unitCube))
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  spatial_H1 : ∀ T : ℝ, 0 < T →
    ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T), CriticalPhysicalH1 (v t) (G t)
  dissipation_integrable : ∀ T : ℝ, 0 < T →
    IntervalIntegrable (fun t => criticalGradientEnergy (G t)) volume 0 T
  energy_initial : ∀ t : ℝ, 0 ≤ t →
    physicalEnergy (v t) + 2 * ν * (∫ r in (0 : ℝ)..t, criticalGradientEnergy (G r)) ≤ ‖a₀‖ ^ 2
  energy_intervals : ∀ T : ℝ, 0 < T →
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T), ∀ t ∈ Icc s T,
      physicalEnergy (v t) + 2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤
        physicalEnergy (v s)

/-- The usual pointwise energy upper bound follows from the actual
nonnegative dissipation integral. -/
theorem CriticalLerayHopf.velocity_energy_le_initial
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalLerayHopf ν a₀ v G) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) :
    physicalEnergy (v t) ≤ ‖a₀‖ ^ 2 := by
  have hd : 0 ≤ ∫ r in (0 : ℝ)..t, criticalGradientEnergy (G r) :=
    intervalIntegral.integral_nonneg_of_forall ht (fun r => criticalGradientEnergy_nonneg (G r))
  have hcoef : 0 ≤ 2 * ν * (∫ r in (0 : ℝ)..t, criticalGradientEnergy (G r)) :=
    mul_nonneg (mul_nonneg (by norm_num) hν) hd
  linarith only [hv.energy_initial t ht, hcoef]

end

end SingularClosure
