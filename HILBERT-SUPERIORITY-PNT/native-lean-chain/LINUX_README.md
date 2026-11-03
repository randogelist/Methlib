# Linux CI for the combined Lean chain

Package the combined directory as `HVR_NATIVE_LEAN_CHAIN.zip`, with a single
top-level directory named `HVR_NATIVE_LEAN_CHAIN`. Put
`hvr_combined_linux.py` in that directory and include its SHA-256 in the
package's `sources.sha256` manifest. Place the ZIP at the repository root and
install `hvr-native-chain.yml` as
`.github/workflows/hvr-native-chain.yml`. Commit both files to a GitHub branch.
Run **HVR native Lean chain (Linux)** from Actions using `workflow_dispatch`,
or push a change to the ZIP or workflow.

The job checks out Mathlib at `fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0`,
checks its Lean 4.34.0-rc1 toolchain, fetches its cache, verifies the package
source manifest, rebuilds all project modules, and audits each named
declaration. The downloadable artifact contains stage logs, source and object
hashes, compiler information, and the result. A passing audit establishes
only the reported theorem and axiom checks; the downloaded Mathlib cache is
not independently verified in full, and dependency independence is not
established. The integrated spectral asymptotic uses the existing theta proof
and the zeta bridge still uses an existing Mathlib identity.

For a plan and manifest check without running Lean, run
`HVR_PACKAGE_ROOT=/path/to/HVR_NATIVE_LEAN_CHAIN python3 hvr_combined_linux.py --check-plan`.
