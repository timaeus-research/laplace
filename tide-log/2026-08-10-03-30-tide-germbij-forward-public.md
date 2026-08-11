# Tide: germbij forward programme stage 7 (public theorems)

**Direction (user):** "Yes continue with germbij... the main core
concern being the recovery of all coefficients in the nondegenerate
case and the main theorem in the nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-division at c865480
(stacked; stage 6 in PR #108). Final stage of the archived design
consult's seven-stage programme.

**Started:** 2026-08-10T03:30Z

## Candidate

`Laplace/Multi/ForwardTheorems.lean`, closing the forward direction:

1. `numeratorCoeff_one_zero_pos`: the partition function's constant
   coefficient ∫ e^{-T₂} is positive (correctionCoeffFn_zero +
   integral_pos_iff_support_of_nonneg + NeZero volume).
2. `momentCoeff` (the division coefficients of numerator by
   partition) and **`rescaledMoment_hasExpansion`**: the rescaled
   posterior moment of any continuous polynomial-growth observable is
   an order-N asymptotic polynomial at 0⁺ — the germbij forward
   direction, at the seabed's rescaledMoment.
3. `monomial_moment_hasExpansion` (the monomialTest instances that
   the inverse-half recovery theorems consume).
4. `momentCoeff_eq_of_isLittleO`: moment families agreeing to o(q^N)
   have equal expansion coefficients through order N (via stage-A1
   uniqueness) — the jet-comparison face.

## Numerical check

Not feasible in closed form (existence-form statements); the
underlying expansions were checked numerically in stages 4 and 6.

## Result

`Laplace/Multi/ForwardTheorems.lean` (~130 lines), all gates green on
the first fix round (IsLittleO.neg is neg_left).
**THE FORWARD PROGRAMME IS COMPLETE.**

- `hasPolynomialGrowth_one`, `numeratorCoeff_one_zero_pos`
  (∫ e^{-T₂} > 0 via support = univ + NeZero volume).
- `momentCoeff`, **`rescaledMoment_hasExpansion`** (the germbij
  forward direction in the nondegenerate case: rescaled posterior
  moments of continuous polynomial-growth observables are order-N
  asymptotic polynomials at 0⁺), `rescaledMoment_expansion_exists`,
  `monomial_moment_hasExpansion`.
- `momentCoeff_eq_of_isLittleO` (jet comparison via stage-A1
  coefficient uniqueness).

Together with the merged inverse half (PRs #93-#95:
superpolynomially-close moment families determine the location, the
positive-order jet, and for analytic losses the germ), this completes
the germbij note's Theorem 3.1 in the nondegenerate case: the
seven-stage programme (A1 #96, A2 #97, A3 #98, A4 #99, 5a #100,
5b #101, 5c-pre #102, 5c-i #103, 5c-ii-a #104, 5c-ii-b #106, 6 #108,
7 this PR) ran start to finish in one session arc.

### Suggested follow-ups

- Marker pass on germbij.tex (blue-dot \leanref tags for the forward
  theorems + pin bump) once this merges.
- SRI docs sync (projects.json lean description, lean/README.md,
  local germbij README).
- Deferred (less crucial per the user): semi-quasi-homogeneous
  constructive class; explicit Wick coefficient VALUES (the existence
  form suffices for the note's theorem; values would connect
  momentCoeff to Isserlis data).
