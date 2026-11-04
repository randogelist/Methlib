# HVR–Zetahyperbolic integration candidate

The package rebuilds the theta PNT root with the direct prime-mode Mellin
assembly in place of its direct LSeries_eq_mul_integral call. It also builds
finite prime Gram and Jacobi identities, their actual matrix bridge, a
downstream prime-mode Mellin assembly, and a conditional finite-frequency
bridge with explicit weighted frequency bounds. See
HVR_ZETAHYPERBOLIC_INTEGRATION_A_TIER.txt for exact scope and open premises.

The named theorems passed the cached Linux Lean 4.34.0-rc1 build and
standard-only axiom audits in
https://github.com/randogelist/Methlib/actions/runs/41744680137 . The exact
additional mode assembly and weighted bounds passed in
https://github.com/randogelist/Methlib/actions/runs/41745623568 .
The actual prime-error weighted moment passed in
https://github.com/randogelist/Methlib/actions/runs/41745700135 .
The actual prime Laplace frequency bounds and weighted finite-frequency
adapter passed in https://github.com/randogelist/Methlib/actions/runs/41746159554 .
The finite-cell error bound passed in
https://github.com/randogelist/Methlib/actions/runs/41746760052 .
Finite-cell aggregation passed in
https://github.com/randogelist/Methlib/actions/runs/41747466498 .
The previously downstream mode assembly was refactored upstream to avoid an
import cycle. The matching 88-source root build and audit passed in
https://github.com/randogelist/Methlib/actions/runs/41747091013 .
The exact
conditional premises remain part of their statements. A named axiom audit does
not establish dependency removal. Windows execution of this package is pending.
The intended toolchain uses a populated Mathlib cache at revision
fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0.

