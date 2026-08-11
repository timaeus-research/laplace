# Tide: germbij degenerate recovery, the separable germ

**Direction (user):** standing auto-mode commission; the last
consult-flagged germbij follow-on (degenerate strata beyond
dimension one, note section 7.4).
**Seabed:** laplace, main at a2103ef (post-monomial-tests).
**Started:** 2026-08-09T16:30 local

## Candidates v1 (Claude)

The minimal 7.4(b) germ: SEPARABLE weighted-monomial potentials
L(x) = sum_i a_i x_i^{2 k_i} on EuclidD d, where the Gibbs measure
is a product of the 1D measures already fully understood.

1. **Factorization**: coordinate (products of even-power) moments
   over EuclidD d factor into 1D closed forms — normalized moments
   are EXACT power laws t^{-sum_i j_i/k_i} times Gamma ratios; the
   note's exponent-affinity l(alpha) affine in alpha holds exactly.
2. **Weight recovery**: matched coordinate second-moment data forces
   k_i = k_i' per coordinate (1D power-law rigidity coordinate-wise;
   the note's q_i = (l(2e_i) - l(0))/2 in the exact separable case).
3. **Scale recovery**: given matched k_i, the a_i also agree (1D
   base recovery per coordinate). Together: the first constructive
   recovery statement at a degenerate minimum in dimension > 1.

Rationale: every analytic ingredient is merged 1D material; the new
content is the product bridge (the catalogued unconditional Fubini
idiom) and the statement design. Scoping consult in flight
(pi type vs EuclidD, staging, and whether a non-separable
quasi-homogeneous example would be a better first step).

## GPT-5.6 Sol v1

Archived verbatim in `tide-log/gpt56_degenerate_scoping_v1.md`.
Summary: statements correct (with the normalized/unnormalized
exponent-affinity distinction made explicit: normalized l(alpha) is
linear, l(0) = 0; the note's (l(2e_i) - l(0))/2 formula is the
unnormalized convention); pi type (Fin d -> R / general Fintype
iota) is the right home for the analytic core with EuclidD wrappers
later; the coordinate-marginal theorem + coordinate second-moment
recovery is "probably the highest value-to-effort first milestone";
x^4 + x^2 y^2 + y^4 rejected as first step (common weights, no
factorization, abandons the 1D seabed); roadmap: (1) coordinate
marginal, (2) recovery, (3) EuclidD transport, (4) multi-index
affinity, (5) abstract anisotropic scaling, (6) Gelfand-Leray.

## Vote

- Claude: candidates 1-3 as one tide (= consult roadmap items 1-2).
- GPT-5.6 Sol: same. Agreed.

## Numerical check

Executed before this text was written (scipy quad, 2D separable
L = 1.5 x^4/4! + 0.7 y^6/6!, t = 50):

    coord-1 second moment: 1D numeric = 0.1911955190
                           closed form = 0.1911955190
                           2D product  = 0.1911955190
    coord-2 second moment: 1D numeric = 0.8724928888
                           closed form = 0.8724928888
    k=2: moment ratio t->4t = 2.000000, 4^(1/k) = 2.000000
    k=3: moment ratio t->4t = 1.587401, 4^(1/k) = 1.587401

Closed form, 1D reduction, and the recovery exponent all agree to
ten digits.

## Result

Committed on tide/germbij-degenerate-separable:
`Laplace/Multi/SeparableRecovery.lean` (~300 lines). Theorems:
1D helpers `gibbsExpectation_smul_kthPotential`,
`secondMoment_smul_kthPotential` (exact power law with coefficient
`((2k)!/a)^(1/k) * Gamma(3/(2k))/Gamma(1/(2k))`),
`secondMoment_coeff_pos`, `kth_secondMoment_recovery`; multivariate
`separableMonomial`, `exp_separableMonomial`,
`partitionFunction_separableMonomial`,
`coordSq_integral_separableMonomial` (one-hot factorization),
`gibbsExpectation_coordSq_separableMonomial` (coordinate reduction,
spectator cancellation), and `separableMonomial_recovery`: matched
coordinate second-moment data on a temperature ray forces k1 = k2
and a1 = a2 — the first constructive recovery at a degenerate
minimum in dimension > 1. Zero sorries, zero warnings.

Surprises: the worktree was created from a stale local main (the
canonical clone had not yet pulled the previous tide's merges), so
the first build was vacuous for the new file until a rebase onto
origin/main — the "verify the import AND the olean" gate caught it;
lesson: `tide-worktree create` bases on the canonical clone's main,
so pull canonical BEFORE creating a stacked-on-latest worktree. One
prefix-collision from a careless replace-all (OneD.partitionFunction
is a prefix of OneD.partitionFunction_kthPotential_pos). The rpow
bookkeeping (t*a absorption) was contained, as the consult
predicted for the separable route.
