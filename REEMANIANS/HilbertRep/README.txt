HXY_THREE_SPACES_433_v0_1_0_PASS
MODE := A_TIER_DERIVATION
VERIFIED_SOURCE_PACKAGE := HXY_THREE_SPACES_433_v0_1_0_FIX6
VERIFIED_SOURCE_REVISION := FIX6
POST_VALIDATION_LEAN_CHANGES := 0
AGGREGATE_TIER := A_TIER
AGGREGATE_CLOSURE := UNCONDITIONAL_CLOSURE
AGGREGATE_MARKER := !!!!
AGGREGATE_SCOPE := exact conjunction of the four frozen equivalence statements

EXACT ROOT
  (forall X Y : Nat, HXY X Y <-> RiemannHypothesis)
  /\ (RiemannHypothesis <-> BanachExt)
  /\ (RiemannHypothesis <-> HilbertRep)
  /\ (RiemannHypothesis <-> HolExt).
  Declaration := HXY_THREE_FUNCTION_SPACE_EQUIVALENCES.
  Explicit research premises := NONE.
  Unresolved obligations of this exact equivalence root := NONE.

EXACT COMMON CONSTRUCTION
  RiemannHypothesis -> BanachExt /\ HilbertRep /\ HolExt.
  Declaration := HXYThreeSpaces.all_three_of_nativeRH.
  Marker := !!!!(cond on RH).
  Input := RiemannHypothesis only.
  Additional unresolved construction obligations := NONE.

CURRENT PROMOTIONS
  C1_CLOSURE=!!!!(cond on RH)
  C1_EQUIVALENCE_A_TIER=!!
  C2_CLOSURE=!!!!(cond on RH)
  C2_EQUIVALENCE_A_TIER=!!
  C3_CLOSURE=!!!!(cond on RH)
  C3_EQUIVALENCE_A_TIER=!!
  ROOT_EQUIVALENCES=PASS
  ROOT_RH_CONSTRUCTIONS=PASS
  RUN=PASS

EVIDENCE
  Origin := user-supplied native console excerpts.
  Latest := provenance/native-transcript-FIX6-pass.txt.
  Prior five endpoint passes := provenance/native-transcript-FIX5-partial.txt.
  Promotion record := provenance/promotion-FIX6.json.
  Current status := STATUS.json.
  FROZEN_CANDIDATES.json status fields := historical freeze-time values.
  Axiom dependencies subset := {propext, Classical.choice, Quot.sound}.

DELIVERABLES
  HXY_THREE_FUNCTION_SPACE_EQUIVALENCES.lean
  HXY_THREE_FUNCTION_SPACE_EQUIVALENCES_A_TIER.txt
  HXY_THREE_FUNCTION_SPACE_EQUIVALENCES_B_TIER.txt
  HXYThreeSpaces/*.lean
  run.cmd
  RUNNER_NOTES.txt
  FROZEN_CANDIDATES.json
  provenance/frozen-sources.json
  provenance/new-sources.json

NATIVE CACHED REPRODUCTION
  cd /d "%USERPROFILE%\Downloads" && tar.exe -xf "HXY_THREE_SPACES_433_v0_1_0_PASS.zip" && call "HXY_THREE_SPACES_433_v0_1_0_PASS\run.cmd"
  Compiler := Lean 4.33.0, native Windows x86_64.
  Dependencies := existing pinned Mathlib cache.
  Compatible project-module receipts := REUSED.
  RUNNER_POLICY := TRUSTED_FAST_V2.
  RUNTIME_HASHING := DISABLED.
  RECURSIVE_DEPENDENCY_INVENTORY := DISABLED.
  LOCAL_ASSISTANT_LEAN_EXECUTION := NONE.
  Observed FIX6 cache reuses := 106.
  Observed FIX6 successful new project-module compilations := 4.

SCOPE
  Equivalence root := unconditional relative to the approved standard axioms.
  Witness construction := conditional on RH.
  Premise-free RH := NOT_CLAIMED.
  Textbook GRH / finite-witness checker equivalence := outside this root.

HISTORICAL REPAIR RECORDS
  The following statuses record preparation-time observations.
  Current authoritative status := the PASS record above and STATUS.json.

FIX2
  Native diagnostic source: provenance/native-failure-v0_1_0.txt.
  C1: explicit identity scalar homomorphism reduction.
  C2: bundled-map reduction, real/complex coercions and inner-product identities.
  C3: explicit analytic composition, inverse cancellation and germ reduction.
  Frozen candidates and endpoint signatures: unchanged.
  Cached successful module receipts: reused under the same cache family.
  External FIX2 compilation and audits: pending.

FIX3
  Explicit rfl evaluation lemmas for the C1 and C2 bundled linear maps.
  Norm bounds rewrite those lemmas before applying the retained estimates.
  Candidate predicates, root endpoints, pins and cached runner: unchanged.
  External FIX3 compilation and audits: pending.

FIX4
  Preserve C1 and C3 proof sources from FIX3.
  Observed: C1 forward/reverse module passes; C3 forward matching cache hit.
  Parse standard axiom names carrying explicit Lean universe annotations.
  Preserve the exact three-name axiom allowlist and fresh endpoint audits.
  Repair the C2 integral-positivity theorem name, function-power normalization,
  and scoped exponent-notation failure.
  External FIX4 compile/audit results and promotions: pending.

FIX5
  Remove optional-capture dependencies from the native JScript axiom parser.
  Reproduce the FIX4 propext failure under legacy capture semantics, then verify
  both modern and emulated legacy modes against the same strict allowlist.
  Repair C2 reverse identity evaluation, scalar casts and field notation.
  Preserve all forward modules and all C1/C3 proof sources byte-for-byte.
  Compatible compilation cache remains enabled; runtime hashing remains disabled.
  Native FIX5 theorem-level audits and remaining reverse compilation: pending.

FIX6
  Native FIX5 evidence: C1/C2 exact equivalences PASS; C1/C2/C3 forwards PASS.
  Standard-only theorem-level axiom audits and exact-type checks PASS for
  those five named endpoints. Their source/dependency closures are preserved.
  C3 reverse: normalize m+1 versus 1+m in the finite analytic-order argument.
  Changed Lean scope := entire_local_ode_nonvanishing, hbad proof body only.
  Runtime runner, compiler pins, cache family and audit policy := UNCHANGED.
  Matching compiled modules := REUSED; no runtime hashing.
  External FIX6 C3 equivalence and aggregate audits := PENDING.

FIX6 EXTERNAL COMPLETION
  C3 equivalence := PASS.
  Exact public conjunction := PASS.
  Exact common RH construction := PASS.
  All theorem-level audits := STANDARD_ONLY.
  Source edits following this validation := NONE.
