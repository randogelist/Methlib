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
QFA endpoint package v0.3.0: 91 theorem candidates and two proof-carrying
linear-isometry constructions. Four analytic proposition targets retain no
supplied proof inhabitants. Import QFA.Assembly for the four reusable assembly
interfaces. The frozen physical QFA root remains a separate B-tier target.
External cached Windows Lean 4.33.0 compilation and exact axiom audits pending.
-/
