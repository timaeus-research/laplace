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

## GPT-5.6 Sol v1

Archived verbatim in `tide-log/gpt56_onepoint_shape_v1.md`. Rulings:
the function-level C(t) model is faithful AS the flat-equivalence
consequence (present it so, not as a definition of series equality);
the quantifier order `exists C, forall phi` is essential (the other
order has almost no content); C needs NO regularity at all (never
integrated or differentiated); normalize the anchor lower bound to
an integer exponent (avoids rpow arithmetic against the `forall N :
Nat` decay definition); the moment upper bound should be
`IsBigO atTop (I phi) (fun _ => 1)` with `int |phi|` as the cheap
witness; exact anchor equality can even be weakened to superpoly
difference (local equality supplies exact, keep it). Minimal first
tide = pure SuperPoly algebra: (1) anchor cancellation
SuperPoly((C-1)A) + A >= kappa t^-n => SuperPoly(C-1); (2) gauge
removal SuperPoly(C-1) + J = O(1) + SuperPoly(B - C J) =>
SuperPoly(B - J); (3) packaged one-observable corollary. No measure
theory, no analyticity, no support bookkeeping. Next tide: moment
boundedness + local anchor instantiation + the thin final wrapper on
the merged contradiction theorem.

## Vote

- Claude: the consult's minimal first tide (SuperPoly def + the two
  cancellation lemmas + packaged corollary).
- GPT-5.6 Sol: same (its own staging). Agreed.

## Numerical check

Not feasible: pure asymptotic-inequality algebra over the IsLittleO
API, no closed form to evaluate. (The downstream Laplace content was
numerically checked in the tides that produced it.)
