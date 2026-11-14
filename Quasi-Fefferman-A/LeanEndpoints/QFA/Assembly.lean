import QFA.Assembly.Representation
import QFA.Assembly.Restart
import QFA.Assembly.AnalyticInputs
import QFA.Assembly.Comparison
import QFA.Assembly.AnalyticChain
import QFA.Assembly.TailComparison
import QFA.Assembly.Chain
import QFA.Assembly.Integrated

/-!
# QFA composed endpoint chain, v0.4.0

Canonical parameterized implication:
`QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs`.

LC004 + LC001 + LC003 -> actual real-field pointwise absorption;
explicit strong-reference construction and class/comparison realization ->
selected subcritical restart -> comparison -> restricted tail singleton.
LC002 follows conditionally from LC001 through the spectral moments.

LE001-LE093 retain their verified proof bodies. LE094-LE108 are prepared
candidates until the matching external compiler and axiom audit pass.
The post-verification ledger and immutable CI records identify actual status.
No smoothness, pressure, actual LH realization, or physical QFA root closure
is inferred from the explicitly parameterized class/reference implication.

Execution: cached native Windows Lean 4.33.0 in GitHub Actions only.
-/
