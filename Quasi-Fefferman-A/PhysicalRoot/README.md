# QFA Physical Root

```text
THEOREM = QFA.PhysicalRoot.QUASI_FEFFERMAN_A
PREPARED_STATUS = A_TIER_CANDIDATE
TARGET_STATUS = CONDITIONAL_FORMAL_CLOSURE
MARKER_AFTER_VERIFICATION = !!!
LOCAL_LEAN_EXECUTIONS = 0
```

The package is an immutable copy of the externally verified LE001–LE108 QFA
source tree plus the exact physical-root implication LE109–LE112.

## Canonical theorem

```lean
import QUASI_FEFFERMAN_A

#check QFA.PhysicalRoot.QUASI_FEFFERMAN_A
```

The theorem concludes the frozen root predicate:

\[
\forall a\in H,\quad
\mathrm{LH}_\nu(a)\ne\varnothing,
\]

\[
\forall u\in\mathrm{LH}_\nu(a),\quad
u(t)\to a\ \text{in }L^2\ \text{as }t\downarrow0,
\]

and, for every

\[
\delta>\frac{\|a\|_2^4}{16\pi^2\nu^5},
\]

\[
\mathrm{SmoothNSETail}(\nu,u,\delta)
\quad\land\quad
\mathrm{LH}_\nu(u(\delta))
=
\{\tau\mapsto u(\delta+\tau)\},
\]

where the final equality is represented exactly on nonnegative elapsed time.

## Named unresolved premises

`ClassRealization`, `ReferencePorts`, LC004, LC001, LC003,
`ReferenceConstructionFromAbsorption`, and `SmoothReferencePorts`.

`SmoothNSETail` is the explicit semantic parameter whose intended
instantiation is existence of pressure and smooth velocity-pressure
representatives satisfying the unforced incompressible NSE on the tail.

## External execution

```cmd
root-run.cmd
```

The runner is restricted to native Windows Lean 4.33.0. It compiles and audits
the verified 108-declaration baseline and the four root declarations. No local
Lean or Lake execution is performed.
