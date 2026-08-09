# Tide: germbij location recovery (nondegenerate core, item D)

**Direction (user):** the nondegenerate core; audit consult (archived
in the expansion-bridge tide log) item D.
**Seabed:** laplace, stacked on tide/germbij-expansion-bridge
(PR #93, unmerged at start).
**Started:** 2026-08-10T00:30 local

## Candidates

Per the audit consult section 4 (deliberation of record):

1. Anchored coordinate-moment limit: posteriorMoment (w i) q -> 0
   (from the merged q^-1 E[w_i] -> 0 by multiplying back the q).
2. Located moments: for a loss anchored at 0 and a location c, the
   located moment is the anchored moment of the translated
   observable; the honest translated-integral form recorded via
   measure translation invariance. Located coordinate moments tend
   to c_i (observable splits as c_i + y_i; integrand additivity;
   spectator normalization).
3. Two-loss location equality: superpolynomially matched located
   first-moment families force c1 = c2 (limits along t -> infinity
   through the q = (sqrt t)^-1 substitution; uniqueness of limits).
   "The observable family must contain the uncentered coordinate
   functions" — hence located moments at uncentered coordinates.

## Vote

- Claude: as staged. - GPT-5.6 Sol: section 4 of the audit consult
  is exactly this staging. Agreed on record.

## Numerical check

Not feasible: structural limit plumbing over merged components.
