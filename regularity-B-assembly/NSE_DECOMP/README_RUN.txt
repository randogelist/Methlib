NSE_DECOMP v0_1_9 FIX2 FASTCACHE
=====================================
COMPILER ERROR FIX: At former line 1285, ht : t ∈ Set.Ioi 0 was
passed directly to le_of_lt. The input is now elaborated explicitly:
    change (0 : Time) < t at ht
    exact le_of_lt ht
This is a definitional unfolding of Ioi membership, not a new premise.

Native Windows Lean 4.34.0-rc1 required, matching precompiled Mathlib.
No local Lean execution, download, lake update, build or cache-get by packaging.

After extracting into %USERPROFILE%\Downloads, run:
  call "%USERPROFILE%\Downloads\NSE_DECOMP_A_TIER_CANDIDATE_v0_1_9_FIX2_FASTCACHE\run.cmd"

Existing Mathlib workspace override:
  call "%USERPROFILE%\Downloads\NSE_DECOMP_A_TIER_CANDIDATE_v0_1_9_FIX2_FASTCACHE\run.cmd" -MathlibProject "C:\path\to\cached-lake-project"

Runner invokes installed Lean via lake env without building dependencies;
uses 16 Lean threads (override NSE_DECOMP_THREADS), and SHA256 sealed
incremental reuse for matching successful native external audits.
On BUILD=FAIL, prints compiler errors and stores run-error-summary.log.

This change has not been compiled in the requested native toolchain.
Verification remains A_TIER_CANDIDATE.  E : AnalyticEndpoints and
B : FourierCoefficientL2Bound are explicit unresolved premises.
The exact physical PDE semantics and unconditional root remain open.
