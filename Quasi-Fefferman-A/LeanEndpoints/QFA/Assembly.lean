import QFA.Assembly.Representation
import QFA.Assembly.Restart
import QFA.Assembly.AnalyticInputs
import QFA.Assembly.Comparison

/-!
# QFA reusable endpoint assembly

`import QFA.Assembly` exposes four independent, explicitly scoped interfaces:

* Representation: supplied compact-test derivatives and their L2 Laplacian sum;
  conditional compact-to-Schwartz and spectral composition.
* Restart: selected subcritical time, shifted energy profile, weak pairing
  continuity and strong initial trace.
* AnalyticInputs: supplied physical norm estimates to scalar absorption.
* Comparison: a.e. comparison starts and common traces to nonnegative-time
  equality; singleton only after restriction to the physical time domain.

All new proof bodies remain A_TIER_CANDIDATE. The analytic endpoint arguments,
physical witness identification, weak momentum equation, local/global strong
solution theory, cross-testing, smoothing and pressure require their stated
realization proofs. No declaration here asserts the frozen physical QFA root.

External execution: cached native Windows Lean 4.33.0; exact axiom audits.
Local Lean/Lake executions: zero.
-/
