import QFA.Endpoints.Agmon.Contracts
import QFA.Endpoints.Agmon.Scalar
import QFA.Endpoints.Comparison.AdmissibleTimes
import QFA.Endpoints.Comparison.RelativeEnergy
import QFA.Endpoints.Composition.GoodTimeAndTrace
import QFA.Endpoints.Composition.GoodTimeOfEnvelope
import QFA.Endpoints.Energy.ProductBudget
import QFA.Endpoints.GoodTime.Basic
import QFA.Endpoints.GoodTime.Cutoff
import QFA.Endpoints.GoodTime.Interval
import QFA.Endpoints.Representation.Complexification
import QFA.Endpoints.Representation.EnergyProfile
import QFA.Endpoints.Restart.EnergyShift
import QFA.Endpoints.Restart.HilbertTrace
import QFA.Endpoints.Restart.TimeTranslate
import QFA.Assembly

/-!
QFA v0.4.0: 108 exact audit roots, 106 theorem declarations and two
proof-carrying isometry constructions. Import QFA.Assembly for the full chain.
LE001-LE093 have prior matching external evidence. New LE094-LE108 remain
candidates until the matching current-source CI audit passes. Source headers
record preparation status; the recorded CI evidence is authoritative.
The physical QFA root remains B_TIER_ROOT_FORMALIZATION_PENDING.
-/
