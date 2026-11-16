import SingularClosure.SixChannelProjections
import SingularClosure.SixEnergy
import SingularClosure.HilbertChannels
import SingularClosure.SmoothSixSynthesis
import SingularClosure.SmoothSixEnstrophy
import SingularClosure.Ax6ExactBudget

/-!
# VAR_STABLE six-channel endpoint collection

Existing exact channel reconstruction, orthogonality, weighted spectral
Pythagoras, physical/spectral identification, and square-budget conversion.
-/

set_option autoImplicit false

namespace SingularClosure
namespace VAR_STABLE

#check SIX_CHANNEL_PROJECTIONS
#check SIX_CHANNEL_SPECTRAL_ENERGY_EQ
#check TORUS_L2_SIX_CHANNEL_RECONSTRUCTION
#check TORUS_L2_SIX_CHANNEL_ORTHOGONAL
#check TORUS_L2_SIX_CHANNEL_PYTHAGORAS
#check smoothSixChannel_finiteSynthesis
#check SIX_CHANNEL_REAL_ENSTROPHY_EQ
#check SIX_CHANNEL_ENSTROPHY_EQ
#check AX6_EXACT_REAL_SQUARE_BUDGET
#check AX6_EXACT_PHYSICAL_SQUARE_BUDGET

end VAR_STABLE
end SingularClosure
