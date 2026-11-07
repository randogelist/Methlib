# Erdős #687 — Attempt_B

## Exact scope

Finite survivor count S(q,y,a) = #{i<y : gcd(|a+i|,q)=1}.
Gram(q,y,E) = diagonal matrix of the counts on shifts E.
Det Gram = product of S(q,y,a), hence det Gram>0 iff every tested shift survives.
Positivity propagates monotonically from y to z≥y.

External quantitative input: OpenAI's Jacobsthal theorem from
openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a,
adapted to the actual Erdos687.Y statement by
pw/erdosproblemaday-verification@634b667ee7844f12590117c4c2d7bc0143f2fdd9.

Formal endpoint declarations:
- MethlibErdos687.AttemptB.jacobsthal_spectral_bound
- MethlibErdos687.AttemptB.jacobsthal_no_cover
- MethlibErdos687.AttemptB.erdos_687_part_ii
- MethlibErdos687.AttemptB.erdos_687_quantitative

The little-o(x^2) result is from the pinned external bridge, not a new independent
solution. The near-linear O(x^(1+o(1))) estimate remains unresolved.

## Certification

Run .github/workflows/erdos-687-attempt-b.yml.
Source files are A_TIER_CANDIDATE until the matching GitHub Actions compiler
and theorem-level standard-axiom audit both pass. Linux CI only; do not infer
native Windows A_TIER evidence or compatibility with Lean 4.34.0-rc1.
