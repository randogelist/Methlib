FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0

TARGET
======
One unified A-tier closure atlas for all four exact Fefferman alternatives
in the concrete Real analysis regime.

No new PDE theorem is claimed.

CANONICAL ENDPOINTS
===================
A <-> WholeSpaceZeroForceGlobalRegularity
B <-> PeriodicZeroForceGlobalRegularity
C <-> WholeSpaceForcedBreakdown
D <-> PeriodicForcedBreakdown

NEW PACKAGING
=============
MasterABSemantic :=
  WholeSpaceZeroForceGlobalRegularity
  AND PeriodicZeroForceGlobalRegularity

MasterCDSemantic :=
  WholeSpaceForcedBreakdown
  AND PeriodicForcedBreakdown

ABCDPhysicalEndpoints :=
  all four endpoints

ABCDPhysicalPort :=
  named proof fields for all four endpoints

TARGET THEOREMS
===============
MasterABSemantic <-> A AND B
MasterCDSemantic <-> C AND D
ABCDPhysicalEndpoints <-> A AND B AND C AND D
ABCDPhysicalPort <-> A AND B AND C AND D

This means a future
  MasterAC -> MasterCDSemantic
construction can terminate immediately in C AND D via the unified closure.

Run:
cd /d "%USERPROFILE%\Downloads" && tar.exe -xf "FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip" && call "FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0\run.cmd"
