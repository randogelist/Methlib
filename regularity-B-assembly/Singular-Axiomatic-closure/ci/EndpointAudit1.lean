import SingularClosure.SixChannelProjections
set_option autoImplicit false
set_option Elab.async false
open SingularClosure
noncomputable section
example : PhysicalSixChannelProjectionLaws := SingularClosure.SIX_CHANNEL_PROJECTIONS
#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_PROJECTIONS"
#check @SingularClosure.SIX_CHANNEL_PROJECTIONS
#print axioms SingularClosure.SIX_CHANNEL_PROJECTIONS
end
