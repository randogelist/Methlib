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

### `COMPUTATIONAL_REDUCTION_CELL_CERTIFICATES_B_TIER.txt`

Defines a sound finite-cell reduction for one shell escalation step. For every computational cell `C_k`, certify

```text
MASS2(b) ≤ m_k                  for every b ∈ C_k,
STRONG_WINDOW_ν(b,τ_k)          for every b ∈ C_k,
8π² I² ν⁵ τ_k > m_k².
```

Together with verified shell coverage, these certificates imply

```text
ADMISSION(I) ⟹ ADMISSION(J).
```

The robust strong-window certificate is reduced to the exact a posteriori inequalities

```text
α_k < 1,
4 β_k η_k < (1 - α_k)²,
```

for the error equation

```text
w = F_{k,b} + L_k(w) + Q_k(w,w).
```

Critical noncompactness is not suppressed: it is isolated in one of the named interfaces

```text
TAIL_QUOTIENT_REDUCTION(I,J),
PROFILE_PACKET_REDUCTION(I,J),
CERTIFICATE_GENERATOR(I,J).
```

The resulting root chain is

```text
APOSTERIORI_WINDOW_CERTS
+ MASS2_INTERVAL_BOUNDS
+ TAIL_OR_PROFILE_REDUCTION
+ SHELL_COVERAGE
⟹ COMPUTATIONAL_REDUCTION(I,J)
⟹ OVERLAP_SHELL(I,J)
⟹ ADMISSION(I) → ADMISSION(J).
```

### `H12_RADIAL_FIRST_CONTACT_MINIMUM_B_TIER.txt`

Replaces the informal “angle” by the exact boundary minimization object. With normalized data

```text
b = ν r ω,
‖ω‖_{Ḣ¹ᐟ²} = 1,
```

define the certified permeability

```text
Q_lower(r,ω) := 2 S_lower(r,ω) / ‖ω‖₂⁴
```

and its sphere minimum

```text
M(r) := inf_ω Q_lower(r,ω).
```

The most restrictive boundary datum is an active minimizer of `Q_lower`. The required inherited radius and radial reserve are

```text
B(r) := r M(r)^(-1/4),
D(r) := r - B(r).
```

Thus

```text
M(r) > 1  ⇔  B(r) < r  ⇔  D(r) > 0.
```

A finite obstruction must be a first contact `M(r*) = 1`. The differential propagation certificate is

```text
M(r₀) > 1,
M'(r) ≥ -a(r)(M(r)-1),
a ∈ L¹_loc
```

which implies `M(r) > 1` for every finite radius. Combined with lower-semicontinuity, profile compactness, and the QFB overlap adapter, this yields

```text
r → ∞ ⇔ I = r²/(2π) → ∞ ⇒ NSE_B.
```

The exact active-profile target is the `RADIAL_FIRST_CONTACT_RESISTOR` system: constrained stationarity in `ω`, equality `Q_lower = 1`, and nonpositive radial envelope derivative.

## Status

`! B_TIER` derivations only. No prepared endpoint in this directory is promoted to `A_TIER` without matching external Lean compiler and theorem-level axiom-audit evidence.
