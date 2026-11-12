import SingularClosure.CriticalSerrinUniqueness

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
    (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
    (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + gradient (p r) x =
        ν • laplacian (u r) x)
    (hu_trace : Tendsto
      (fun t => eLpNorm (u t - (a₀ : Vec → Vec)) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (T : ℝ) (hT : 0 < T)
    (hSerrin : MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioc (0 : ℝ) T))) :
    ∀ t ∈ Ioc (0 : ℝ) T, v t =ᵐ[volume.restrict unitCube] u t :=
  @SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON ν hν a₀ v u G p hv hu hp hpp hNSE hu_trace T hT hSerrin

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON"
#check @SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
#print axioms SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON

end
end SingularClosure
