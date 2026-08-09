# Tide: germbij-leading-part

**Direction (user):** continue the germbij arc (auto mode): the multivariate
leading-part instantiation, producing the scaled set S (with its amplitude
bound at small scales) from a continuous homogeneous leading part P of
degree m, nonzero in some direction, with remainder O(||x||^{m+1}). This
feeds `sector_lower_bound_multi` and is the last follow-up on the arc's
list.

**Seabed:** laplace, chained off tide/germbij-turnkey (PR #28 pending);
contains the full germbij arc through the turnkey theorem.
**Started:** 2026-08-09T04:35Z
**Worktree/branch:** laplace-tide-germbij-leading-part /
tide/germbij-leading-part

## Deliberation

Final follow-up of the analytic/corollary/turnkey sequence, deliberated in
outline across those tides' retrospectives (the "cap of directions where
the leading part is bounded away from zero"). Multivariate analytic order
theory is not in Mathlib (analyticOrderAt is one-variable), so the
factorisation is taken as the hypothesis pair (homogeneous P, remainder
bound O(||x||^{m+1})), which is what a multivariate Taylor expansion
supplies. Construction: normalise the good direction to norm 3/2
(hypothesis), take S = closedBall(x0, delta) inside the annulus where
|P| >= |P x0|/2 by continuity, and let u0 kill the remainder:
|a(u x)| >= u^m |P x| - C (2u)^{m+1} >= (|P x0|/4-ish) u^m. Elementary; no
fresh consult (statement shape mirrors the 1D instantiation, whose
deliberation and the sector-multi consult cover the design).

## Numerical check

Instance: d = 2, a(x, y) = x^2 y^2 + x^5 (P = (xy)^2, m = 4, remainder
x^5 with |x^5| <= ||x||^5 sup-norm, C = 1). x0 = (3/2, 3/2): P x0 =
(9/4)^2 = 5.0625, c1 = 2.53. On closedBall(x0, 1/2) (sup): |P| >= min at
corner (1,1): P = 1 < c1! So delta must come from continuity, not the full
1/2: with delta = 0.1: min |P| over ball ~ (1.4^2 * 1.4^2) = 3.84 >= 2.53
ok. u0 <= c1/(2*(1*2^5+1)) = 2.53/66 = 0.038. At u = 0.038, x = (1.4,1.4):
|a(ux)| = u^4*3.84 - u^5*5.38 >= u^4(3.84 - 0.2) > (c1/2) u^4 = 1.27 u^4 ok.
Checked arithmetically (hand); the bound is conservative as designed.

## Result

`Laplace/Multi/LeadingPart.lean`, registered in `Laplace.lean`. Declaration,
sorry-free, zero warnings:
- `Laplace.leading_part_scaled_set`: from a continuous P homogeneous of
  degree m under nonnegative scalings, P x0 <> 0 at ||x0|| = 3/2, and
  |a - P| <= C ||x||^{m+1} for ||x|| <= 2 u1, produces S (a closed ball in
  the annulus, measurable, positive finite volume), c > 0, u0 > 0 with
  c u^m <= |a (u . x)| for x in S, u in (0, u0]. Exactly the data
  `sector_lower_bound_multi` consumes.

Three compile iterations: a stray rw against a set-abbreviation (replaced
by direct term), the relocated triangle-inequality lemma (now via
`abs_sub_abs_le_abs_sub` + `abs_sub_comm`), and a long-line lint. Full
`lake build` passes; `scripts/sorries` 0/0/0/0.

Operational note: a parallel session is actively running tides on this repo
(branch tide/sextic-j-function appeared mid-tide; its rebase output leaked
into this session's shell via the shared .git). No interference with this
tide's branch; main's reflog verified clean.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-04-35-tide-germbij-leading-part.tex
