import SingularClosure.NoetherClosure.Root

set_option autoImplicit false
set_option Elab.async false

open SingularClosure

-- Native external theorem-level audit; no local Lean execution authorized.
example : NOETHER_CHARGE_ADMISSION → AX6Statement := NOETHER_TO_AX6
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NOETHER_TO_AX6"
#check @SingularClosure.NOETHER_TO_AX6
#print axioms SingularClosure.NOETHER_TO_AX6

example : NOETHER_CHARGE_ADMISSION → Fefferman_B_0_adjust := NOETHER_CLOSURE
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NOETHER_CLOSURE"
#check @SingularClosure.NOETHER_CLOSURE
#print axioms SingularClosure.NOETHER_CLOSURE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NOETHER_UNIFORM_PHYSICAL_ENSTROPHY"
#check @SingularClosure.NOETHER_UNIFORM_PHYSICAL_ENSTROPHY
#print axioms SingularClosure.NOETHER_UNIFORM_PHYSICAL_ENSTROPHY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NOETHER_SIX_CHANNEL_MATCH"
#check @SingularClosure.NOETHER_SIX_CHANNEL_MATCH
#print axioms SingularClosure.NOETHER_SIX_CHANNEL_MATCH

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NOETHER_UNIFORM_SIX_ENSTROPHY"
#check @SingularClosure.NOETHER_UNIFORM_SIX_ENSTROPHY
#print axioms SingularClosure.NOETHER_UNIFORM_SIX_ENSTROPHY
