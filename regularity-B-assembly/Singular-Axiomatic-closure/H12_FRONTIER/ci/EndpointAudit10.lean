import SingularClosure.PeriodicPressureRecovery
set_option autoImplicit false
set_option Elab.async false
open SingularClosure Set MeasureTheory Filter Metric
open scoped BigOperators Interval ContDiff ENNReal Topology
noncomputable section
example : ∀ {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha),
    GlobalSmoothNSE ν a L.velocity L.pressure ∧
      ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency,
        (∫ x in unitCube, star (fourierCharacter k x) * (L.pressure t x : ℂ)) =
          if k = 0 then 0 else
            -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
              (∑' p : Frequency, (L.state 0 t).val p i * (L.state 0 t).val (k - p) j)) /
                (∑ i : Fin 3, (k i : ℂ) ^ 2) :=
  @SingularClosure.PERIODIC_PRESSURE_RECOVERY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.PERIODIC_PRESSURE_RECOVERY"
#check @SingularClosure.PERIODIC_PRESSURE_RECOVERY
#print axioms SingularClosure.PERIODIC_PRESSURE_RECOVERY
end
