# Tide: germbij thm:singular end-to-end composition, part 1 (prep)

**Direction (user):** Adversarial GPT-5.6 Sol critique of the
unnormalized degenerate theorem (archived verbatim as
`tide-log/gpt56_singular_critique_v1.md`), then explicit user
approval (2026-08-10) of: minimal TeX fixes (done locally: the
N = m + d/2 integer phrasing at both sites, the coverage footnote
softened to the critique's twelve-step list), archiving the critique,
and closing the composition gap — machine-checking thm:singular end
to end.

**Seabed:** laplace main at 0e12c2d. The critique's section B4 is the
plan: twelve semantic steps between the corpus and the note-level
statement.

**Started:** 2026-08-10T08:20Z

## Candidates (part 1 of ~3: the prep lemmas)

`Laplace/Multi/SingularPrep.lean`:

1. `quadratic_upper_bound_of_nonneg` (critique step 6): K C² at 0,
   K(0) = 0, K ≥ 0 near 0 ⇒ ∃ C₀ ≥ 0, R > 0 with K ≤ C₀‖w‖² on the
   R-ball. Route: IsLocalMin.fderiv_eq_zero kills the gradient;
   ContDiffAt.fderiv_right + exists_lipschitzOnWith makes the
   derivative M-Lipschitz near 0; the hasFDerivWithin mean-value
   bound on the ‖w‖-ball of g := K - K(0) - f'(0)· gives
   K(w) ≤ M‖w‖².
2. `exists_least_nonzero_diagonal` (critique steps 4-5): from
   HasFPowerSeriesOnBall g p 0 r, g(0) = 0, and g ≢ 0 on the ball,
   produce the least m with nonzero diagonal, the vanishing of all
   lower diagonals, and x₀ with p_m(x₀,…,x₀) ≠ 0 and ‖x₀‖ = 3/2.
   KEY SIMPLIFICATION over the critique's polarization plan: the
   power-series sum evaluates ONLY diagonals (HasFPowerSeriesOnBall
   .hasSum), so "all diagonals vanish ⇒ g ≡ 0 on the ball" is direct
   and no symmetric-multilinear polarization is needed; m ≥ 1 comes
   from coeff_zero = g(0) = 0, x₀ ≠ 0 from map_coord_zero, and the
   3/2 normalization from map_smul_univ homogeneity.
3. `exists_bump_one_on_ball` (critique step 7): the ContDiffBump
   wrapper producing continuous, compactly supported, nonnegative ψ
   with ψ = 1 on the R-ball.

Parts 2-3 (subsequent tides): the composed point theorem (translation
to an arbitrary p, the expansion-family bridge and integral
rewriting, negation → contradiction) and the locus theorem
(compactness point selection + neighborhood assembly).

## GPT-5.6 Sol

The adversarial critique is the deliberation: its B4 list is followed
step for step, with the polarization dissolution noted above as the
one deviation (a simplification; the diagonal-only observation).

## Vote

- Claude: the three prep lemmas as part 1.
- GPT-5.6 Sol (via the critique's B3/B4): the same selections;
  polarization listed there as "not mathematically problematic" and
  here avoided outright.

## Numerical check

Structural lemmas (existence of constants/witnesses); not feasible,
and the quantitative content downstream was verified in the original
identifiability arc and re-audited by the critique.

## Result

`Laplace/Multi/SingularPrep.lean` (~200 lines), all gates green
(three fix rounds):

- `quadratic_upper_bound_of_nonneg` (critique step 6):
  IsLocalMin.fderiv_eq_zero + ContDiffAt.fderiv_right +
  exists_lipschitzOnWith + the hasFDerivWithin mean-value bound on
  the ‖w‖-ball give K ≤ M‖w‖² with M the derivative's Lipschitz
  constant.
- `exists_least_nonzero_diagonal` (steps 4-5): the constant diagonal
  vanishes upfront (hasSum_single at 0 + map_coord_zero), Nat.find
  then lands at degree ≥ 1 without dependent-index transport, and
  map_smul_univ rescales the witness to ‖x₀‖ = 3/2. No polarization.
- `exists_bump_one_on_ball` (step 7): the hand-rolled
  min/max/norm bump — continuous, compact support inside the
  (R+1)-ball, nonneg, ≡ 1 on the R-ball; avoids smooth-bump instance
  requirements entirely (the endpoint needs only continuity).

The TeX fixes approved alongside this work are applied locally to
germbij.tex (both N = m + d/2 sites now integer-quantified; the
coverage footnote states the twelve-step reduction honestly);
compiles clean.

Surprises: ContDiffAt.differentiableAt now takes `n ≠ 0` not
`1 ≤ n`; interval_cases on a set-bound Nat.find index tangles with
dependent Fin types (restructure: prove the degenerate case's fact
generally FIRST, then rewrite inside Nat.find_spec); EMetric.ball is
deprecated for Metric.eball on this pin.

### Suggested follow-ups (parts 2-3)

- Part 2: the composed point theorem — translation to an arbitrary
  p (substitution invariance of the pencil integrals), the
  expansion-family bridge and integral rewriting (critique steps
  10-11), and `pencil_families_force_germ_eq_at`.
- Part 3: the locus theorem — compactness point selection (step 1)
  and neighborhood assembly (step 12).
