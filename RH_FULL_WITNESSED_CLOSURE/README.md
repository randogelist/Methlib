# RH_FULL_WITNESSED_CLOSURE

Fail-closed CI admission scaffold for a future finite coordinate witness.

## Current state

`RH_WITNESS_STATE=EMPTY`.

The workflow currently proves only:

- the actual-xi witness architecture compiles against pinned dependencies;
- a deliberately wrong coordinate packet is rejected by Lean;
- no concrete witness or unconditional RH root is present;
- the maximum displayed marker is `!!!`.

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
