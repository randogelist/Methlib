import HVRComplexExpIntegralDirect
import HVRPrimeLeftFull
import HVRPrimeFiniteFrequencyDirect
import HVRPrimeRightCompactSupport
import HVRPrimeWeightedFrequencyApproximation

/-! Build-only aggregation of the unintegrated candidate lemmas. -/

namespace HVRFubiniCandidateLane
/-- Marker for selecting this build-only lane; not a Fubini theorem. -/
theorem lane_marker : True := trivial
end HVRFubiniCandidateLane
