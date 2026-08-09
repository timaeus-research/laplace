# Tide: germbij expansion bridge (nondegenerate core, item B)

**Direction (user):** continue with germbij, do not switch seabeds;
consult on highest-value remaining targets, the core being recovery
of all coefficients and the main theorem in the nondegenerate case.
**Seabed:** laplace, main at b3b2d69.
**Started:** 2026-08-09T23:30 local

## Audit + consult

A full audit of the nondegenerate story against the note found the
merged recovery theorems consume o(q^(k-2)) moment-RATE hypotheses
while the note's Theorem 3.1 takes equality of expansion FAMILIES;
also missing: location recovery (everything anchors the minimum at
0), the analytic-germ corollary, and the entire FORWARD direction
(existence of the all-orders expansion with jet-determined
coefficients). Audit consult archived verbatim in
`tide-log/gpt56_nondegen_audit_v1.md`; its strategic ranking
B > D > A > C > E with implementation order B, D, C then the
six-stage programme A. Explicit caveat adopted: B+C alone would NOT
justify claiming Theorem 3.1 formalised; B+D+C completes the inverse
half, A is the remaining substantive half.

## Candidate (this tide = B)

The SuperPoly data bridge, per the consult:

1. `posteriorMoment` (t-level normalized localized moment as a
   function of q via the merged dilation identity
   posteriorIntegral_eq; prefactors q^d e^{-L0/q^2} cancel in the
   normalized quotient).
2. Homogeneity identity: for degree-k homogeneous P,
   posteriorMoment P q = q^k * rescaledMoment P q.
3. Filter bridge: Tendsto (q^2)^{-1} atTop along nhdsWithin 0 Ioi;
   SuperPoly f (in t) implies all q-rates of q -> f(q^{-2});
   division by a fixed power q^m preserves all rates (the consult's
   closure lemma, needed because of the q^k homogeneity prefactor).
4. Headline `smooth_jet_recovery_of_superPoly_moments`: packages +
   base + symmetry + SuperPoly-matched t-level monomial moment
   families imply equal jets at all orders — the merged recovery in
   the note's own "same asymptotics" language.

## Vote

- Claude: B as staged. - GPT-5.6 Sol: B first, exactly this shape
  (the audit consult IS the deliberation). Agreed.

## Numerical check

Not feasible: structural (filter substitution + identity plumbing
over numerically-verified components).
