# Source provenance and scope

**Direct-mode root:** The full 90-stage canonical build and named standard-only
axiom audits passed in cached Linux
[run 41748517704](https://github.com/randogelist/Methlib/actions/runs/41748517704)
at commit `673d97bd2fc7b4d80fda00b84de8b82072e340c7`. Its
[evidence artifact](https://github.com/randogelist/Methlib/actions/runs/41748517704/artifacts/13285471045)
records source/object hashes and diagnostic outputs. An earlier matching
88-module proof-chain run was
[41747091013](https://github.com/randogelist/Methlib/actions/runs/41747091013).
The prior 86-stage Abel-root run below is historical. Windows execution
of this revised source remains unverified. Mathlib sum-integral and
change-of-variable infrastructure remain.

The direct-mode diagnostic detected six direct/two-hop positive controls.
It found the prime-mode theorem and original wrapper in the actual root;
it did not see the prior Abel helper or Mathlib LSeries_eq_mul_integral
there. Negative trace coverage remains unverified. It found Mathlib's
von Mangoldt log-derivative theorem in the root. The 90-stage run's DCT
diagnostic detected all four positive controls and found both selected
dominated-convergence declarations in the revised root.


## Mellin integration and checked scope

`HVR_PrimeMellin_Abel.lean` adapts the `f 0 = 0` Abel-summation case of
`Mathlib/NumberTheory/LSeries/SumCoeff.lean` from Mathlib revision
`fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0`. Its source preserves the
upstream attribution; the Apache 2.0 text is in `LICENSE-MATHLIB.txt`.
The existing Mellin theorem statements and premises are preserved, while
the earlier proof called that helper. The helper retains Mathlib's general
Abel-summation and analysis infrastructure; the current root uses
the prime-mode route instead.

The earlier 86-stage source was built and its named declarations were
standard-only axiom audited under cached Linux Lean 4.34.0-rc1 in
[run 41742938933](https://github.com/randogelist/Methlib/actions/runs/41742938933)
at commit `688397970101fa1a0e43c1f46b34a931ff10eb74`. Its artifact is
[13281534383](https://github.com/randogelist/Methlib/actions/runs/41742938933/artifacts/13281534383).
The checked helper source SHA-256 was
`939eaae7a226e79c47d7915a22715995010d94344eafd4b02f36ee547486d93d`;
the modified Mellin source SHA-256 was
`476cc82171e5e8ff457198959e4a4eafa84617c4b3af8e8f4182251b24dd2b66`.

The direct and two-hop positive controls were detected. The trace did not see
`LSeries_eq_mul_integral` in the helper, the checked callers or the final
root. Zero reached theorem bodies and zero declarations were reported missing
for those roots, but negative dependency coverage remains unverified; no
semantic independence is claimed. The run's separate DCT root diagnostic still
found both selected dominated-convergence declarations. The positive-control diagnostic
is separate and must not be imported into the proof chain. The prior
half-line runs predate this change and do not certify these changed sources.

These additions consolidate the HVR source packages developed alongside the original `HILBERT-SUPERIORITY-PNT` project. The original half-line source is replaced as described in HALFLINE_REPLACEMENT.md. `original_sources.sha256` is retained as historical provenance; `branch_sources.sha256` is the input lock used for the PNT job.

- `native-lean-chain/` is the extracted source of `archives/HVR_NATIVE_LEAN_CHAIN.zip`, exactly the original archive tracked on the development branch. It includes the six prime-spectral modules and its own source manifest, build plan and Linux/Windows runners. Its named-theorem Linux build and axiom audit passed in [run 41688856236](https://github.com/randogelist/Methlib/actions/runs/41688856236). Consult the individual theorem signatures: an audit of a conditional implication does not discharge its hypotheses.
- `prime-spectral-amendment/` preserves the six branch source files, their exact audit plan, source hashes and native Windows runner. They are built also in the combined chain above. Their zeta-linked statements still use Mathlib infrastructure, including an existing von Mangoldt/zeta endpoint in the audited source.
- `native22-rebuild/` preserves the earlier 22 candidate source modules, plan, manifests and runners. The extracted folder omits bundled build evidence and compiled objects; the complete original package, including its earlier evidence, is preserved as `archives/HVR_NATIVE_22_CALL_CANDIDATES_RC1.zip`. A previous Linux run is [41697649026](https://github.com/randogelist/Methlib/actions/runs/41697649026); individual theorem scopes and hypotheses still matter.
- `native-rebuild/` preserves the candidate Lean sources and plan extracted unchanged from `archives/HVR_NATIVE_REBUILD_CANDIDATES.zip`, the exact latest source archive from development commit `9f9c42ef45cf5ae0bb8822d6ef5a25b51daacea4`. Its Linux runner was adapted for an explicit known-target dependency policy, documented in `known-dependencies.json`. Its 26 modules and 41 named declarations compiled and had standard-only axiom audits in [run 41712052899](https://github.com/randogelist/Methlib/actions/runs/41712052899). The exact bridge `HVRNextEulerPrimeZetaBridge.eulerProductLogDerivative` concerns a totalized prime-indexed `tsum` and actual Riemann zeta on `Re(s) > 1`. The run overall failed its separate full dependency gate because named transitive dependencies were detected. Negative dependency-trace coverage remains unverified; no full Mathlib independence is claimed.

The zeta-bridge replacement has **not** been substituted into the original PNT theorem. In particular, the original PNT source `HVR_Zeta_LogDerivative.lean` directly invokes Mathlib's existing `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. These source packages therefore do not establish that the entire PNT development is independent of the selected Mathlib results.

`archives/` retains the two exact source ZIP blobs that were tracked on the development branch and the complete earlier 22-candidate ZIP. That earlier archive includes its original verification evidence, including compiled objects; no `.olean` files or build-evidence directories are tracked in the extracted source folders. The extracted folders are the inspectable versions. Each package's `.gitattributes` preserves byte-exact source and plan hashes across checkouts. Mathlib-derived proof sources retain attribution and use the Apache 2.0 license included with `native-rebuild/`.

All Lean jobs use Lean `4.34.0-rc1` and the Mathlib revision `fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0` where specified in their workflows. Cached compiled Mathlib libraries are required.

Four further conversation deliverables are preserved byte-for-byte in `archives/`: `HVR_PRIME_POWER_REINDEXING.zip`, `HVR_DEPENDENCY_REDUCTION.zip`, `HVR_SIMPLE_NATIVE_DERIVATIONS.zip`, and `HVR_NATIVE_SIMPLE_NEXT.zip`. They include their historical CI evidence and runner status; their source revisions are distinct, and no full PNT integration is implied.
