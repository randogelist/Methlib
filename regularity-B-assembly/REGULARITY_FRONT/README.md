# S_DIR_L2_GLOBAL_REGULARITY — REGULARITY_FRONT

Canonical theorem name: `S_DIR_L2_GLOBAL_REGULARITY`  
Repository path: `regularity-B-assembly/REGULARITY_FRONT`  
Package: `S_DIR_L2_GLOBAL_REGULARITY_433_v0_9_1_INFINITE_SERRIN_FIX1`  
Compiler target: native Windows Lean 4.33.0 with existing Mathlib cache.  

## Scope and certification

- Previously compiled: the 12 source modules through `S_DIR_L2_SERRIN_FINITE.lean`;
  external report `PROJECT_BUILD=PASS`, `THEOREM_AXIOM_AUDITS=63`,
  `AXIOMS=STANDARD_ONLY`.
- New module: `S_DIR_L2_SERRIN_INFINITE.lean` — **A_TIER_CANDIDATE**.
  FIX1 repairs the v0.9.0 error at line 93 by using
  `Measurable.pow_const` instead of applying the proposition-level power
  method incorrectly.
- No other Lean module was modified.
- The root `S_DIR_L2_GLOBAL_REGULARITY` is still a **definition/target**, not
  an unconditional Lean proof. Physical torus synthesis and unrestricted
  Leray–Hopf uniqueness remain open.

## Local native cached run

From this folder, in Windows CMD:

```cmd
call run.cmd "%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1"
```

The runner creates evidence logs inside `evidence/`, uses source-keyed `.olean`
cache for all unchanged modules, and audits the exact registered theorem roots.
Do not interpret prepared source as A-tier before matching compiler/audit PASS.

## Files

13 Lean source modules, `run.cmd`, `support/run.ps1`, mathematical B-tier
documentation, previous candidate registers, and `SHA256_MANIFEST.txt`.

No Lean compiler was executed while preparing this package.
