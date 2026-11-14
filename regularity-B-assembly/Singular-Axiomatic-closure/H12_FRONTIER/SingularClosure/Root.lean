import SingularClosure.PeriodicPressureRecovery

/-! The frozen root implication. AX6 remains an explicit unresolved hypothesis. -/

set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure

/-- Frozen endpoint 11. Every downstream analytic edge is an actual theorem
body. The sole unresolved admission is the explicitly supplied AX6 statement. -/
theorem ax6_implies_fefferman_B_0_adjust : AX6Statement → Fefferman_B_0_adjust := by
  intro hAX6 ν hν a ha
  obtain ⟨L⟩ := GALERKIN_GLOBAL_STRONG_LIMIT hAX6 ν hν a ha
  exact ⟨L.velocity, L.pressure, (PERIODIC_PRESSURE_RECOVERY L).1⟩

end SingularClosure
