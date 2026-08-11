# Tide: germbij-jet-variance (weighted-jet programme, stage 1)

**Direction (user):** germbij Section 7.4 inductive recovery (auto
mode, standing delegation): the weighted-jet programme, recovering
each coefficient c_r of L = a x^{2k} + Σ c_r x^{2k+r} inductively
from the graded corrections at t^{-r/(2k)}. Stage 1: variance of
monomial observables against the pure even-monomial Gibbs weight —
Gamma closed forms and strict positivity, the injectivity input for
every recovery rung.

**Seabed:** laplace, main at 5cffa8c (Prop 4.1 + witness complete).
**Worktree/branch:** laplace-tide-germbij-jet-variance /
tide/germbij-jet-variance
**Started:** 2026-08-10T02:25Z

## Programme scoping

Consult saved verbatim: `tide-log/gpt56_weighted_jet_scoping_v1.md`.
Four candidate programmes were considered: (A) the delta rung (fifth
cumulant), (B) general-order 1D Theorem 3.1, (C) multivariate
Theorem 3.1 first rung, (D) Section 7.4 inductive a_j recovery.
GPT-5.6 Sol recommends (D) as a finite weighted-jet theorem
(L = a x^{2k} + Σ_{r≤R} c_r x^{2k+r}, explicit coercivity envelope),
ranking (A) safest fallback, (C) strategically valuable but a
foundations programme, (B) deferred until (D) de-risks it. Eight
stages listed in dependency order; the named scope trap is treating
the bare finite jet as globally integrable (highest term may be odd
or negative — the analytic envelope must be chosen before the
combinatorics). Claude concurs: (D) has the smallest infrastructure
delta per rung (the generalized-Gaussian moment API already exists in
MonomialPotential.lean) and its normalized-series machinery de-risks
(B).

## Vote (programme)

- Claude: programme (D), staged per the consult.
- GPT-5.6 Sol: programme (D) ("best balance of novelty, existing
  machinery, and tide-sized closure").

Agreed.

## Candidate v1 (Claude), stage 1

Seabed survey: kth_moment_even/odd, partitionFunction_kthPotential
(+_pos), gibbsExpectation_kthPotential_even/odd, kth_integrable_pow
(_pot) already cover the consult's Tide-1 moment API for the
reference weight e^{-t x^{2k}/(2k)!}. What is missing is exactly the
injectivity input:

1. monomial_variance_odd / monomial_variance_even: Gamma closed forms
   for Var(x^n) = gibbsCov (kthPotential k) t x^n x^n (odd n: the
   mean vanishes, Var = the even moment; even n: difference of Gamma
   ratios).
2. monomial_variance_pos (the heart): 0 < Var(x^n) for n ≥ 1, k ≥ 1,
   t > 0 — the note's own argument (Var[Q] = 0 forces Q constant
   against a measure of full support), realized as: Var =
   (∫ (x^n − M)² e^{-tL_k})/Z with the centered integrand continuous,
   nonneg, and of open nonempty support, hence positive integral.

## Numerical check

Executed before formalisation (scipy quadrature).
(1) Programme-level (the consult's prescription): the q^r coefficient
of E_q[u^{2k+r}] responds to c_r with slope -Var_mu(u^{2k+r}),
independent of lower coefficients. Measured/predicted ratios at
q = 0.05, dc = 1e-4: k=1 r=1: 1.0015; k=1 r=2: 1.0062; k=2 r=1:
1.0008; k=2 r=3: 1.0028 (finite-difference error, converging in q).
Both odd and even 2k+r included per the parity warning.
(2) Tide-level: Var(u^j) numeric vs Gamma form for
mu ~ exp(-t x^{2k}/(2k)!), k ∈ {1,2}, t ∈ {2.0, 1.5}, j = 1..4:
agreement to 6 decimals at every point, all positive (e.g. k=1 j=3:
1.875000 = 15/8 · (2/t)^3 scaling; k=2 j=4: 64.000000).

## Result

- Theorems (Laplace/OneD/MonomialVariance.lean, ~215 lines, zero
  sorries, zero warnings): `monomial_variance_odd` (odd monomial: mean
  vanishes, variance = the even moment in Gamma form),
  `monomial_variance_even` (difference of Gamma ratios under the
  common (2k)!/t power), and the heart, `monomial_variance_pos`:
  0 < Var(x^n) for k ≥ 1, n ≥ 1, t > 0, by the note's own injectivity
  argument — Var = (∫(x^n − M)² e^{-tL_k})/Z with the centered
  integrand continuous, nonnegative, of open nonempty support
  (witness x = 1 when M = 0, x = 0 otherwise).
- Surprises: (1) `ring` DOES normalize symbolic exponent arithmetic
  (x^(2n) vs (x^n)² with n free) — the planned two_mul/pow_add
  rewrites were not only unnecessary but harmful (two_mul matched
  2*M first). (2) `simp only [defName]` cannot unfold a def (use
  `unfold`); fun_prop then handles the monomial potential. (3)
  positivity cannot conclude ≠ 0 through (−M)² without knowing
  M ≠ 0; explicit mul_ne_zero chains are cleaner for support
  witnesses.
