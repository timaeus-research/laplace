# Tide: germbij-analytic

**Direction (user):** continue the germbij arc and annotate the note with
formalisation markers as theorems land. This tide: the analytic-germ
instantiation, deriving the factored sector hypothesis `c * w^m <= |a w|` on
`Icc 0 r0` from `AnalyticAt R a 0` with nonzero germ (finite
`analyticOrderAt`), which connects the merged quantitative chain (PRs
#21-#25) to the analytic setting of germbij Theorem 7.3.

**Seabed:** laplace, main at 5c02350 (full germbij arc, 1D + multivariate).
**Started:** 2026-08-09T02:55Z
**Worktree/branch:** laplace-tide-germbij-analytic / tide/germbij-analytic
(base verified 5c02350 at creation, per the stale-main lesson of the
previous tide)

## Seabed snapshot

The five merged germbij tides. All statements carry the analytic input as
the factored hypothesis `c * w^m <= |a w|` (or its scaled-set analogue).
Mathlib provides `analyticOrderAt (f : K -> E) (z0) : ENat` with
`AnalyticAt.analyticOrderAt_eq_natCast : analyticOrderAt f z0 = n <->
exists g, AnalyticAt K g z0 /\ g z0 <> 0 /\ (f =_eventually fun z =>
(z - z0)^n • g z)` (Mathlib.Analysis.Analytic.Order), which is exactly the
factorisation the germbij note invokes ("analyticity enters only through
finite vanishing order").

## Candidates v1 (Claude)

**A (instantiation lemma, 1D).**
```
theorem analytic_growth_lower_bound (a : R -> R) (ha : AnalyticAt R a 0)
    (hne : analyticOrderAt a 0 <> top) :
    exists (m : N) (c r0 : R), 0 < c /\ 0 < r0 /\
      (analyticOrderAt a 0 = m) /\
      forall w in Set.Icc (0 : R) r0, c * w ^ m <= |a w|
```
Proof sketch: m := analyticOrderNatAt a 0; factor a =_ev z^m * g with g
analytic, g 0 <> 0; c := |g 0|/2; continuity of g at 0 gives |g| >= c on a
ball of radius r1; the eventual equality holds on a ball of radius r2;
r0 := min r1 r2; for w in [0, r0]: |a w| = w^m |g w| >= c w^m.
Rationale: the minimal statement that discharges the factored hypothesis of
`sector_lower_bound` (and, at scale, of the composite bounds) from an
analytic hypothesis; zero new infrastructure beyond Mathlib's Order file.

**B (payoff corollary, 1D analytic identifiability).** Compose A with
`pencil_difference_lower_bound`: for L1, L2 >= 0 analytic at 0 with
L1 + L2 <= C0 w^2 near 0 and g = L2 - L1 of nonzero germ, exists m, c such
that for all t >= 4/r0^2 (and integrability + bump hypotheses) the
polynomial lower bound holds. Rationale: the note-facing statement; but the
quantifier bookkeeping (constants before t, hypotheses at scale) makes it a
second step. Attempt only if A lands cleanly.

## Numerical check

Not feasible as a single number (the statement is existential); the
downstream inequality it feeds was checked in the previous tides
(margins 25x, 162x, 5e5, 8e6). Sanity instance: a(w) = w^2 (1 + w)/2:
order m = 2, g = (1+w)/2, g(0) = 1/2, c = 1/4, any r0 <= 1: indeed
w^2/4 <= |a w| on [0, 1].

## GPT-5.6 Sol v1

(consult launched; formalisation proceeds concurrently per the arc's
precedent, corrections integrated on arrival)

## GPT-5.6 Sol v1 (returned)

Saved verbatim: `gpt55_germbij-analytic_v1.md`. Verdict: A correct and
appropriately stated; `analyticOrderAt a 0 <> top` is "the most API-friendly
expression of nonzero analytic germ". Its two proof cautions (take r/2 to
avoid the endpoint of the strict-inequality ball; simplify the factorisation
via sub_zero + smul_eq_mul + abs_mul + multiplication monotonicity) match
the implementation exactly, which compiled on the first attempt while the
consult ran. VOTE: A.

## Vote

- Claude: A (with B, the composed analytic identifiability corollary, only
  if A lands with budget to spare).
- GPT-5.6 Sol: A ("the missing reusable bridge from finite analytic order
  to the already-merged quantitative hypothesis"; B as a short subsequent
  composition).

Agreed: A.

## Result

`Laplace/Analytic.lean`, registered in `Laplace.lean`. Declaration,
sorry-free:
- `Laplace.analytic_growth_lower_bound`: from `AnalyticAt R a 0` and
  `analyticOrderAt a 0 <> top`, produces m (= the analytic order), c > 0,
  r0 > 0 with `c * w^m <= |a w|` on `Icc 0 r0`.

Compiled on the first attempt, zero warnings. Full `lake build` passes;
`scripts/sorries` 0/0/0/0. Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` supplied the factorisation with no
friction; `eventually_gt_nhds` + `ContinuousAt.abs` + 
`Metric.eventually_nhds_iff` the radius extraction. Candidate B (the
composed 1D analytic identifiability corollary) deferred to a follow-up
tide per the vote.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-02-55-tide-germbij-analytic.tex
