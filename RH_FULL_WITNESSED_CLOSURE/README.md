# RH_FULL_WITNESSED_CLOSURE

Fail-closed CI admission scaffold for a future finite coordinate witness.

## Concrete coordinate testing

`CoordinateTesting.lean` implements a terminating, data-only test of an exact
finite specification. `run.cmd` accepts `coordinates/example.json` by default,
or one supplied JSON path:

```bat
run.cmd
run.cmd "C:\path\coordinates.json"
```

The input schema is the existing `RawCert`: integer numerators, natural
denominators, cutoff/split coordinates, near/cell/tail records and finite
payload lists. The host parser emits only numeric Lean constructors. Lean
then proves `CoordinateWellFormed submittedCoordinate` with `by decide`.

The scoped checker tests positive denominators, exact rational order, a
single cell covering `[etaSplit, 1]`, matching cutoffs and split coordinates,
ordered advertised bounds, and the finite G2/G3 sign alternatives. All
comparisons use integer arithmetic. No actual-xi enclosure is inferred from
the advertised rational labels; `proofData` remains opaque.

The native runner requires Python 3.10+ and installed Windows Lean 4.33.0.
It uses the compiler's bundled Std cache and hash-matched project objects;
it performs no network access, Lake invocation or Mathlib rebuild. The
separate Windows workflow compiles fresh project objects first and repeats
the run using its matching cache. Every run performs theorem-level axiom
audits and checks that a deliberately invalid admission fails.

```text
FINITE_COORDINATE_TESTING=A_TIER_FINITE_SCOPE
EXPECTED_FINITE_CONCLUSION=CoordinateWellFormed submittedCoordinate
ACTUAL_XI_ENCLOSURE_VERIFICATION=OPEN
RH_COORDINATE_ADMISSION=NOT_ESTABLISHED
```

The new finite theorem is documented in `CoordinateTesting_A_TIER.txt`.
Native Windows Lean 4.33.0 compilation, theorem-level audits (only
`propext`), negative admission and matching cache replay passed in
[run 42342213966](https://github.com/randogelist/Methlib/actions/runs/42342213966),
at source revision `b3baf95d8fede82b4b3abd395889828fe2eef2fd`.
The verified Lean source files are unchanged by this evidence update.
A pass of the finite testing workflow never establishes RH admission.

## Current state

`RH_WITNESS_STATE=EMPTY`.

The RH scaffold workflow is intended to check:

- the actual-xi witness architecture compiles against pinned dependencies;
- a deliberately wrong coordinate packet is rejected by Lean;
- no concrete witness or unconditional RH root is present;
- the maximum displayed marker is `!!!`.

The inspected base revision's workflow failed at the source-manifest check
before Lean compilation. This revision refreshes that manifest. Neither the
manifest repair nor the finite coordinate checker supplies the missing
`ConcreteSystem.lean`: actual near-boundary/cell/tail soundness and the
`NativeAnalyticPremises` fields still require proofs. `PROMOTION_CAP=!!!`
is a publication ceiling, not evidence that this revision achieved `!!!`.

The existing local experimental environment used Lean 4.33.0 with no network
or Lake during native replay. Its negative control evaluated the wrong packet
to `false` and rejected admission exactly as intended.

## Later candidate handshake

After a local packet passes, commit in one candidate revision:

1. `witness/candidate.hex` — canonical finite packet;
2. `witness/candidate.sha256` — SHA-256 of decoded bytes;
3. `ConcreteSystem.lean` — closed `concreteSystem : ClosedSystem`;
4. `RH_FULL_WITNESSED_CLOSURE.lean` — copy of the frozen root template;
5. `STATUS.env` with `RH_WITNESS_STATE=CANDIDATE`.

The CI then independently:

1. rebuilds from pinned Lean/HVR/Mathlib sources;
2. regenerates `GeneratedWitness.lean` from the committed packet;
3. evaluates the concrete Boolean checker;
4. proves witness admission;
5. compiles the exact root
   `RHFullWitnessedClosure.RH_FULL_WITNESSED_CLOSURE :
   _root_.RiemannHypothesis`;
6. rejects `sorry`, `admit`, explicit `axiom`, `native_decide`, `sorryAx`,
   unapproved axioms, endpoint substitution, witness-hash mismatch, and
   unresolved root parameters.

Even after a clean candidate CI pass, repository status remains `!!!` until
independent review of the committed source, packet, exact root, and CI evidence.
Only that later review may authorize `!!!!`.
