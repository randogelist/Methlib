# Hilbert–Superioriority PNT

This directory contains the unchanged Lean sources and Windows runner from
`HVR_PNT_THETA_ASSEMBLY_RC1_FIX2.zip`. The root declaration is
`HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one`, the theta form of the prime
number theorem. The original run reported a passing root build and named
standard-axiom audit; its full Mathlib cache provenance was not recorded.

GitHub Actions uses native Windows Lean `4.34.0-rc1` and Mathlib commit
`de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` (the `v4.34.0-rc1` release),
downloads Mathlib's cache, executes the original runner, and uploads its
evidence. This pinned Mathlib revision is a CI selection, not an identified
match for the earlier external cache. The CI result must be checked separately.

The workflow checks these source hashes before building:

* `HVR_PrimeDensity_FinalRoot.lean`: `69c5ed8806b9cec089e70c4dc7422e5f442feef1d4138b51a355e0475d04423b`
* `Audit_HVR_PrimeDensity_FinalRoot.lean`: `84fbc235a599207ccfcd894a5c47646394c579b1827f70b6078a4664b0ff6136`

The runner records compiler, source and object hashes and checks named theorem
axioms against its allowlist. Hashes establish byte identity, not independent
authentication of a prior run or proof-route independence. An Actions result is
not a pass until the workflow actually completes successfully.

For a local Windows run with an already populated compatible Mathlib cache:

```cmd
set "MATHLIB_CACHE_ROOT=C:\path\to\mathlib"
call run.cmd
```

The original archive SHA-256 is
`1691e27682d7be2dd52fa4cae841d5b73a5034a5f11d4767068a49009f0a7566`.
