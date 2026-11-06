# 025. Chollet’s Hadamard-product permanent inequality

**Area:** Matrix analysis and bosonic computation

**Status:** 🔵 OPEN

**Last checked:** 2026-09-08

## Problem statement

For every $`n\ge1`$ and Hermitian positive semidefinite matrices $`A,B\in\mathbb C^{n\times n}`$, determine whether

```math
\mathop{\mathrm{per}}\nolimits(A\circ B)\le\mathop{\mathrm{per}}\nolimits(A)\mathop{\mathrm{per}}\nolimits(B).
```

The Hadamard product is $`(A\circ B)_{ij}=a_{ij}b_{ij}`$ and $`\mathop{\mathrm{per}}\nolimits(C)=\sum_{\sigma\in S_n}\prod_i c_{i,\sigma(i)}`$. No sign condition on individual off-diagonal entries is imposed.

## Application

Permanents of Gram matrices occur in bosonic interference. A universal product bound would control the effect of combining two Gram structures on the resulting interference weight.

## References

1. F. Zhang, [An update on a few permanent conjectures](https://arxiv.org/abs/1608.02844), 2016; Chollet conjecture section. Statement and history.
2. P. Pant and R. Singh, [On Chollet’s Permanent Conjecture for Graph Laplacians](https://arxiv.org/abs/2604.24192), 2026. New structured real cases.
3. S. Sa-nguansin and K. Rodtes, [Permanents of correlation matrices and the Chollet permanental conjecture](https://doi.org/10.1080/03081087.2025.2588584), Linear and Multilinear Algebra (2025). Correlation-matrix partial results.

## Status review

**Literature check:** Open in cited literature; no later resolution located

Checked on **2026-09-08**. The April 2026 preprint proves graph-structured cases, not arbitrary complex positive semidefinite pairs. Searches also found an August 2026 preprint claiming the inequality through order six; a finite-order result would not settle the universal statement. No all-order resolution was located.

Searches included: `Chollet conjecture 2026 permanent proof`; `Chollet permanent conjecture graph Laplacians`; `Chollet through order six`. This is a documented literature check, not a certification that no solution exists.

