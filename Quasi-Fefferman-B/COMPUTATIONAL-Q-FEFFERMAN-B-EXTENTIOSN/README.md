# COMPUTATIONAL-Q-FEFFERMAN-B-EXTENTIOSN

Parent endpoint: `Quasi-Fefferman-B/`.

This directory contains computational extensions of the conditional Quasi-Fefferman-B closure.

## Frozen hypothesis

`IMPROVEMENT(I)` denotes the reusable improvement hypothesis

```text
‖b‖_{Ḣ¹ᐟ²}² < 2π I ν²  ⟹  Reg_ν(b).
```

Its QFB constants translation is

```text
T_IMPROVEMENT(a, ν, I) = ‖a‖₂⁴ / (8π² I² ν⁵).
```

Thus the squared-threshold gain `I` induces the QFB cutoff gain `I²`.

## B-tier objects

### `IMPROVEMENT_QFB_OBJECTS_B_TIER.txt`

Defines the base `IMPROVEMENT(I)` object, the Leray-Hopf quartic budget, the `H12_SIGMA_0_RESTR_ADAPTER`, structural orbit access, and the exact QFB cutoff law.

### `IMPROVEMENT_TO_INFINITY_OVERLAP_BOOTSTRAP_B_TIER.txt`

Defines the computational escalation architecture

```text
ADMISSION(I)
+ OVERLAP_SHELL(I,J)
⟹ ADMISSION(J).
```

The datumwise overlap certificate is

```text
STRONG_WINDOW_ν(b,τ)
+ τ > ‖b‖₂⁴/(8π²I²ν⁵)
+ ADMISSION(I)
⟹ Reg_ν(b).
```

An unbounded certified shell chain

```text
Iₙ → ∞,
ADMISSION(I₀),
∀n, OVERLAP_SHELL(Iₙ,Iₙ₊₁)
```

implies global `H^(1/2)_{σ,0}` regularity and, under the standard periodic adapters, `NSE_B`.

The preferred dimensionless cell test is

```text
Ω_I(b,ν,τ)
:= 2ντ / (‖b‖₂²/(2πIν²))²
> 1.
```

## Status

`! B_TIER` derivations only. No prepared endpoint in this directory is promoted to `A_TIER` without matching external Lean compiler and theorem-level axiom-audit evidence.
