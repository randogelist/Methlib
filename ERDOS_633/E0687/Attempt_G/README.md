# Erdős #687 — Attempt_G

MODE: A_TIER_DERIVATION
CURRENT_STATUS: A_TIER_CANDIDATE (until matching GitHub Actions compile and exact-root axiom audit PASS).

Sources:
- OpenAI Jacobsthal formalization: https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/Jacobsthal
- External theorem: OAI.Erdos970.Erdos970Final.erdos_970_quadratic
- External Lean: v4.34.1; external Mathlib revision: d13f23b723b8a846827a245b89c10fc7d3f11612.

FiniteBridge.lean:
  Proves, for finite translations A, n,m,
    (forall f : Nat -> Int, 0 <= gramForm A n m f)
    <-> (forall a in A, 0 < survivorCount n m a).
  Also proves the uniform quantitative Gram/coprime adapter from the named
  JacobsthalQuadratic premise.

ExternalRoot.lean:
  Imports the actual external Lean theorem, derives the local
  JacobsthalQuadratic predicate by definitional transfer, then proves:
    Erdos687AttemptG.erdos_687_prime_hankel_external_root.
  This root states m <= C k^2 and no forbidden covering, positive survivors,
  and finite Gram positivity for all n > 0 with at most k prime factors.

CI:
  .github/workflows/erdos-687-attempt-g.yml
  Jobs: unconditional finite bridge, external quantitative import.
  Requires pinned external source, cached Mathlib objects, Lean 4.34.1.
  Exact theorem-level axioms audited against {propext, Classical.choice, Quot.sound}.

Boundary:
  The new Lean root is a COROLLARY OF THE EXTERNAL JACOBSTHAL THEOREM,
  not an independent proof of its quantitative bound.
  The standalone matrix interpolation lemma and explicit Y(x)=o(x^2)
  (CRT + prime-counting asymptotic) are not claimed as roots of this package.
  No new prime gap bound is asserted.

Certification may be promoted only after matching external build and theorem-level
axiom audit. Repository existence or CI launch alone is not A_TIER.
