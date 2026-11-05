# Fefferman B obstruction

We have only shown Fefferman B here - D is left for the reader.

`CondFeffB.COND_FEFF_B_OBSTRUCT` proves the negation of the **v0.25.0 analytic periodic B** endpoint.

```lean
CondFeffB.COND_FEFF_B_OBSTRUCT : ¬ Fefferman.B Fefferman.ConcreteReal.realAnalysis
```

For every viscosity ν > 0, the same admissible periodic datum admits no witness satisfying the package's joint real-analyticity condition through the initial time. The explicit shear is globally smooth and satisfies the classical Fefferman B requirements for this datum. [Root theorem](COND_FEFF_B_OBSTRUCT.lean)

## Proof chain

On the unit torus, the first component of the velocity is

$$
u_1(x,t)=\sum_{k=1}^{\infty} e^{-k-4\pi^2\nu k^2t}\cos(2\pi kx_2).
$$

The other velocity components and the pressure are zero.

| Step | Lean result | Source |
| --- | --- | --- |
| Initial datum | The analytic Fourier profile is periodic and divergence-free. | [Profile](PeriodicShearProfile.lean) |
| Evolution | The shear solves the scalar heat equation. Its spatial slope has a uniform bound. | [Heat equation](PeriodicShearHeat.lean) |
| Initial-time trace | The absolute right derivatives at the origin are Fourier moments. Their growth exceeds every factorial-geometric bound, so the time Taylor radius is zero. | [Trace](PeriodicShearTrace.lean) · [Growth](PeriodicShearGrowth.lean) · [Analytic bound](PeriodicShearAnalytic.lean) |
| Exclusion of all analytic witnesses | The periodic difference-energy estimate forces each candidate velocity to agree with the shear at the origin. Restricting the candidate's analytic velocity to that time line gives a contradiction. | [Energy derivative](PeriodicShearEnergyTime.lean) · [Comparison](PeriodicShearComparison.lean) · [Root](COND_FEFF_B_OBSTRUCT.lean) |

## Verification

The native Windows Lean 4.33.0 run `r-14451-13052-25954` returned `RUN=PASS`. All 32 theorem-level axiom audits passed. The root depends on `propext`, `Classical.choice`, and `Quot.sound`. [Verification record](COND_FEFF_B_OBSTRUCT_A_TIER.txt) · [Exact type checks](Audit.lean) · [Audited declarations](audit-targets.txt)

## Reproduce on Windows

This folder contains the 17 ordered modules, including its own copies of the Fefferman definitions and the v0.25.0 equivalence. The native runner requires Windows Lean **4.33.0** and a compatible compiled Mathlib cache. [Build order](modules.txt) · [Pinned baseline](base/ConcreteABCDUnifiedClosure.lean)

From this folder in Windows CMD, run

```cmd
call run.cmd /keep
```

To select the Mathlib cache explicitly, replace the path below with the directory containing your prebuilt `Mathlib.olean`.

```cmd
call run.cmd /keep /mathlib "C:\path\to\cached\lib\lean"
```

The runner writes `result.txt`, `signature.log`, and `audit.log` under a new `evidence\r-*` directory.
