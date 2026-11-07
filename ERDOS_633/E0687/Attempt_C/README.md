# Erdős #687 — Attempt_C

Repository location: `ERDOS_633/E0687/Attempt_C`.

**Objective:** cached Lean formalization of the exact CRT/BKQR finite rational certificate and eventual conditional composition with the external Jacobsthal solution.

**Core proposition (unconditional mathematical identity):**
`certificateMass P y (spike y) < 1 ↔ EveryShiftSurvives P y`.

**Known external partial result:** `Y(x)=o(x²)`. The optional source `ERDOS_687_EXTERNAL_ADDON.lean` imports `JacobsthalTo687` from 30k30/scholia, which itself imports the OAI Jacobsthal formalization. That upstream source is Lean 4.34.1 / Mathlib `d13f23b7...`, **not** the cached rc1 compiler used for the standalone core. Until an exactly compatible external lane compiles the addon, external composition is **not** audited by this workflow.

**Open:** The stronger frontier `Y(x) ≪_ε x^(1+ε)`, a uniform certificate inequality, and the native `CRTSemanticBridge` endpoint. No claim of a solution to the open problem.

**CI:** [Erdős 687 Attempt_C workflow](https://github.com/randogelist/Methlib/actions/workflows/erdos-687-attempt-c.yml).

The workflow invokes Lean **on GitHub Actions only**, with pinned Lean 4.34.0-rc1 / Mathlib `fd9375dc...`, retrieves the Mathlib object cache, checks source hashes, compiles the source, and verifies the `#print axioms` transcript for four exact theorem endpoints. No local Lean execution is performed.

**Status:** `A_TIER_CANDIDATE` until matching successful CI compiler and named axiom-audit evidence is inspected. Existing external proof does not imply the remaining stronger target.
