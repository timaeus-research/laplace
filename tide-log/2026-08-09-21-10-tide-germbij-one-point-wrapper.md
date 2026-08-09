# Tide: germbij one-point anchoring, the wrapper

**Direction (user):** standing auto-mode commission; second half of
the one-point programme (the consult's "next tide" list, archived in
the parent tide's log).
**Seabed:** laplace, stacked on tide/germbij-one-point (PR #91,
unmerged at start).
**Started:** 2026-08-09T21:10 local

## Candidates

Per the deliberation of record (the parent tide's consult):

1. **Moment boundedness**: for continuous compactly supported phi
   and 0 <= L, |int phi e^{-tL}| <= int |phi| for t >= 0, packaged
   as IsBigO atTop (fun t => int phi e^{-tL}) 1. (Continuity +
   compact support make the integrability free.)
2. **Local anchor instantiation**: Set.EqOn L1 L2 V +
   tsupport phi0 (subset) V give exact moment equality at phi0 for
   every t.
3. **The contradiction wrapper**: under the analytic package of
   analytic_pencil_difference_not_superpolynomial, an anchored
   proportionality (explicit gauge C, SuperPoly proportionality at
   phi0 and at the pencil observable (L2 - L1) psi, sector-shaped
   lower bound at phi0) is contradictory — i.e. normalized
   agreement anchored at one point forces the germs to differ
   nowhere the pencil theorem can see. The moment difference IS the
   pencil quantity by integral linearity (eventual, t >= 0).
4. Optionally the three-line preface lemma: L2 = L1 + c on V + a
   common zero kills c.

## Vote

- Claude: 1-4 as one tide. - GPT-5.6 Sol: staged so in the archived
  parent consult ("the next tide should add..."). Agreed on record.

## Numerical check

Not feasible: composition of verified components (the pencil-sector
lower bound and the anchor algebra were checked in their own tides).
