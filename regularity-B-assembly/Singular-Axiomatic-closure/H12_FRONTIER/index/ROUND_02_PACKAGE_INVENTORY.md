# Round 02 — Package Inventory

## 1. Native package identity

```toml
name = "singular_axiomatic_closure"
fixedToolchain = true
defaultTargets = ["SingularClosure"]
```

```text
LEAN=leanprover/lean4:v4.33.0
MATHLIB=db584cd6d46c92f209a44c0f1c829460d327499d
LEAN_LIBRARY=SingularClosure
ROOT=SingularClosure
```

The copied folder is independently replayable by entering `H12_FRONTIER` and
executing its native Windows runner.

## 2. Build surface

`run.cmd` performs, in order:

```text
Lean-version lock
source-policy check
audit-checker tests
asynchronous scheduler tests
Mathlib cached-object retrieval
Mathlib revision lock
aggregate lake build
critical DAG build
exact-type theorem audit
axiom checker
```

No local Lean execution was performed during indexing.

## 3. Verified package scale

The frozen verification record reports:

```text
critical extension modules = 104
required critical audit modules = 27
extension audited declarations = 33
original endpoint declarations = 171
full package build = PASS
```

These counts describe the certified original snapshot. They are the baseline
for later frontier delta reports.

## 4. Principal directories

```text
H12_FRONTIER/
├─ SingularClosure/               # theorem modules
├─ ci/                            # source, scheduler, exact-type and axiom checks
│  ├─ critical_audits/
│  ├─ critical_modules.txt
│  ├─ critical_required_audits.json
│  ├─ build_critical.py
│  ├─ check_sources.py
│  └─ check_axioms.py
├─ verification/                  # original external evidence manifests
├─ third_party/                   # retained package dependencies
├─ SingularClosure.lean           # aggregate import root
├─ lakefile.toml
├─ lake-manifest.json
├─ lean-toolchain
└─ run.cmd
```

## 5. Two root families

### Physical small-data root

```lean
SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
```

This is the frontier base.

### Frozen unrestricted-data implication

```lean
SingularClosure.ax6_implies_fefferman_B_0_adjust :
  AX6Statement → Fefferman_B_0_adjust
```

This theorem remains conditional on universal `AX6Statement` and is not the
attachment point for `FRONTIER_H12`.

## 6. Aggregate import rule

`SingularClosure.lean` imports both root families. Frontier modules shall be
added after the copied small-data imports and before a new frontier closure
module. The existing aggregate may continue to expose the base unchanged.

## 7. Index delta convention

Every later assembly report records:

```text
base_module_count
frontier_module_count
base_required_audits
frontier_required_audits
base_root_regression
frontier_root_status
```

The base counts are never silently replaced by frontier counts.