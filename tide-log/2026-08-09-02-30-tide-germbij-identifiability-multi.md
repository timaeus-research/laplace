# Tide: germbij-identifiability-multi

**Direction (user):** closing tide of the germbij multivariate phase (auto
mode): the measure-general pencil identity and the R^d composite
identifiability lower bound, completing the germbij Theorem 7.3 core in d
dimensions.

**Seabed:** laplace, branch tide/germbij-sector-multi (linear chain; adds
Laplace/Multi/Sector.lean to the merged 1D arc).
**Started:** 2026-08-09T02:30Z
**Worktree/branch:** laplace-tide-germbij-identifiability-multi /
tide/germbij-identifiability-multi (base tide/germbij-sector-multi)

## Seabed snapshot

The full 1D germbij arc (Pencil, Sector, Identifiability) plus the
multivariate sector bound (Multi/Sector: `sector_window_lower_bound_multi`,
`sector_lower_bound_multi`). Missing for the d-dimensional composite: the
integrated pencil identity is stated over Lebesgue on R only; its proof
(pointwise FTC + `intervalIntegral_integral_swap`) is measure-generic.

## Deliberation (carried over)

The composite is the same 7-step chain deliberated in the pencil tide and
executed in 1D in the identifiability tide; the multivariate consult
(gpt55_germbij-sector-multi_v1.md, on the sector-multi branch) blessed the
scaled-set corollary form this composite consumes. The one new statement is
the measure-generalisation of `pencil_identity_integrated`, which the 1D
proof already supports verbatim (the Fubini lemma is generic in the second
measure). Proceeding on the deliberation of record.

## Candidates

**A (measure-general pencil identity).** In `Laplace/Pencil.lean` (or
sibling): for a measurable space alpha, measure mu (SFinite), same statement
as `pencil_identity_integrated` with `d mu` in place of Lebesgue-on-R.

**B (multivariate composite).** `Laplace/Multi/Identifiability.lean`:
mirror of `pencil_difference_lower_bound` on `iota -> R`: hypotheses as in
the 1D composite with the window `u . S` (u = (sqrt t)^{-1}) and the
scaled-set data (S measurable, finite volume, ||x|| <= 2 on S, amplitude
bound at scale u for g = L2 - L1), psi = 1 on the ball of radius r0.
Conclusion:
```
(volume S).toReal * (c^2 * exp(-(4*C0)) * (t * t^(-(m:R) - d/2)))
  <= integral (g w * psi w) * (exp(-(t L1 w)) - exp(-(t L2 w))) d(volume)
```

## Numerical check

The d = 2 composite: L1 = (w1^2+w2^2)/2, L2 = L1 + (w1 w2)^2, so
g = (w1 w2)^2; on S = [1,2]^2 at scale u: |g(u x)| = u^4 (x1 x2)^2 >= u^4
(m = 4, c = 1); L1 + L2 = w1^2 + w2^2 + (w1 w2)^2 <= 2||w||^2 + ||w||^4
<= 3 ||w||^2 (sup norm, ||w|| <= 1), so C0 = 3, r0 = 1. t = 100:
Delta = int_{[-1,1]^2} g (e^{-tL1} - e^{-tL2}) computed by dblquad
= 5.045e-07 >= vol(S) c^2 e^{-12} t^{1-4-1} = 6.144e-14. Margin ~8.2e6
(scipy; the C0 = 3 sup-norm bound also grid-verified).

## Vote

Deliberation carried over (see above): the composite is the executed 1D chain
against the deliberated multivariate sector corollary. Both parties' standing
votes cover it; no fresh consult.

## Result

Two pieces, both sorry-free, compiled on the first attempt (after one
notation repair):
- `Laplace.pencil_identity_integrated_measure` and
  `Laplace.exp_pencil_ge_scalar` (in `Laplace/Pencil.lean`): the integrated
  pencil identity over an arbitrary s-finite measure, and the scalar
  comparison along the pencil. The only failure mode was notational: a
  trailing `∂μ` after a nested interval integral is parsed as the interval
  integral's measure (type error against `Measure ℝ`), so nested integrals
  with explicit measures must be parenthesised.
- `Laplace.pencil_difference_lower_bound_multi` (in
  `Laplace/Multi/Identifiability.lean`): the R^d identifiability lower bound
  `vol(S) * c^2 * exp(-(4*C0)) * (t * t^(-(m:R) - d/2)) <= Delta_t(g psi)`.
  The sector-bound integrability hypothesis is *derived* (not assumed) from
  the minorant integrability via `IntegrableOn.congr_fun` on the window
  where psi = 1, so the composite carries the same hypothesis count as the
  1D version.

Full `lake build` passes; `scripts/sorries` 0/0/0/0.

Mid-tide infrastructure note: the previous tide's branch had been created
off a stale local `main` (missing the merged 1D arc), which blocked PR #24
and left this chained worktree without `Pencil.lean`; fixed by rebasing
tide/germbij-sector-multi onto origin/main (one import-list conflict), after
which PR #24 merged as c35e492 and this branch was rebased on top. Lesson:
after any merge, refresh the canonical clone's `main` *before* the next
`tide-worktree create`, and verify the new worktree's base commit.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-02-30-tide-germbij-identifiability-multi.tex
