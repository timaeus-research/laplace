# Tide: germbij one-point anchoring (Proposition 7.6)

**Direction (user):** standing auto-mode commission; the note's last
substantive proved-but-unformalised claim.
**Seabed:** laplace, main at adb00ad (degenerate arc complete).
**Started:** 2026-08-09T20:30 local

## Candidates v1 (Claude)

The blocking question was the data structure for "equal asymptotic
expansion families up to a common scalar series C(t)". Proposal sent
to consult: NO series structure — model the note's "~" as
function-level equality up to superpolynomially small error (the
IsLittleO vocabulary already in Laplace.Decay), and C as an actual
function R -> R:

1. **The C ~ 1 cancellation (lemma A)**: from (i) proportionality —
   for every observable phi in the class, (int phi e^{-tL2} -
   C t * int phi e^{-tL1}) superpolynomially small; (ii) one EXACT
   equality at phi0 (a consequence of ratio-recovery at p, taken as
   the hypothesis L1 = L2 on V); (iii) the sector-shaped positive
   lower bound kappa t^gamma <= int phi0 e^{-tL1}; and (iv) the
   near-free constant-in-t upper bound |int phi e^{-tL}| <=
   vol(supp) * sup|phi| — conclude for EVERY phi:
   (int phi e^{-tL2} - int phi e^{-tL1}) superpolynomially small.
2. **Composition (lemma B)**: feed lemma A's conclusion at the
   observable (L2 - L1) psi into
   analytic_pencil_difference_not_superpolynomial for the final
   L1 = L2-near-W0 contradiction shape.

Consult (in flight): faithfulness of the function-level modeling
(question A), hypothesis shapes (B), minimal first tide (C).
