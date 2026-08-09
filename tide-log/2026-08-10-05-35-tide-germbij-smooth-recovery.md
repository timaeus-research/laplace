# Tide: germbij-smooth-recovery (smooth-germ programme, stages C4-C5)

**Direction (user):** the programme's closing tide (auto mode,
standing delegation): the Taylor/stabilizer adapter and the
finite-order smooth recovery — two smooth admissible losses whose
normalized moment data vanishes at the coefficient-sensitive rates
have equal Taylor coefficients through degree D = R + 2.

**Seabed:** laplace, stacked on tide/germbij-taylor-compare (PR #62
in CI at tide start). Linear-chain worktree.
**Worktree/branch:** laplace-tide-germbij-smooth-recovery /
tide/germbij-smooth-recovery
**Started:** 2026-08-10T05:35Z

## Deliberation

Stages C4-C5 specified in the smooth-germ scoping consult (archived
two tides back: tide-log/gpt56_smooth_germ_scoping_v1.md) and refined
by the C3 shape consult. Seabed survey for the one genuinely new
ingredient: Mathlib's `taylor_isLittleO` supplies the Peano remainder
`(f x − taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] (x − x₀)^n` — so C4
is composition: (1) IsLittleO → the comparison's epsilon-radius jet
form; (2) taylorWithinEval at 0 in jet-coefficient shape
(c_i = iteratedDeriv(3+i) f 0/(3+i)!); (3) the stabilized Taylor
polynomial is admissible AND has a positive jet profile (from the C2
stabilizer envelope through the profile factorization); (4) the
L-vs-P comparison via C3 with the M > D stabilizer invisible; (5)
triangle transfer of the data hypothesis from (L₁,L₂) to (P₁,P₂) and
jet_recovery_stable, concluding equal coefficients hence equal
iterated derivatives through D. Documented prior-deliberation path.

## Vote

- Claude: C4-C5 as one closing tide.
- GPT-5.6 Sol (scoping consult): C4 then C5, with C5 "interface
  adaptation" once C3 exists.

Agreed (carried over).

## Numerical check

The composition introduces no new closed form beyond what C3's and
the weighted-jet programme's executed checks cover; the one new
identity class (Taylor coefficients c_i = iteratedDeriv/(factorial))
is definitional. Noted per protocol; the C3 statement-level check
(previous tide log) covers the analytic content end to end.
