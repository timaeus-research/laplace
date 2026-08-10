# Tide: grand composition final (the radial Taylor bound)

**Direction (user):** the follow-up the package-derivation consult
ranked second and this arc's last open Lean item — discharging
htaylor from smoothness alone.

**Seabed:** laplace, branch `tide/germbij-package-wrapper` (stacked;
parent PR #128 merged during the tide, so this PR targets main).

**Started:** 2026-08-10T20:30Z

## Candidate

`Laplace/Multi/RadialTaylorBound.lean`:

1. `ray_iteratedDeriv_at`: the corpus origin-only ray-derivative
   identity generalized to arbitrary parameter values (its
   composition proof is global in the point; only the final map_zero
   step specialized).
2. `exists_taylorRemainder_bound`: globally C^k loss, any ball
   radius R > 0 → ∃ C ≥ 0 with the order-k fixed-ball remainder
   bound. Route: 1D taylor_mean_remainder_lagrange along each ray
   g(s) = L(s•y) on [0,1] with n := k-1;
   iteratedDerivWithin ↔ iteratedDeriv bridging on Icc via
   iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc, works at
   the endpoint 0 too); taylor_within_apply identifies the Taylor
   polynomial with Σ taylorHomogeneousTerm through the ray identity
   at 0; the mean point's value is bounded by the compact-closedBall
   sup of ‖iteratedFDeriv k L‖ (IsCompact.exists_bound_of_continuousOn
   + ContDiff.continuous_iteratedFDeriv) times ‖y‖^k
   (ContinuousMultilinearMap.le_opNorm, product of constants).
   C := M / k!.
3. `higherLaplaceDomainFamily_ofContDiff`: the wrapper with htaylor
   discharged at R := 1 — the certified family from hcont + hgrad +
   hdiag + hH alone.

## GPT-5.6 Sol

The package-derivation consult (tide-log/gpt56_package_derivation_v1.md
on the parent branch) is the deliberation: its Rank-2 plan is
followed step for step (radial identity, 1D Lagrange, compact-ball
bound, coefficient identification), with its flagged friction points
(Icc endpoint bridging, range-k indexing, coefficient normalization)
addressed by iteratedDerivWithin_eq_iteratedDeriv at ContDiffAt,
n := k-1 with Nat.succ_pred, and taylor_within_apply + the ray
identity at 0.

## Vote

- Claude: the three-piece radial tide.
- GPT-5.6 Sol (via the consult's Rank 2): the same plan.

## Numerical check

Not feasible: an existence-of-constants bound (the quantitative
Taylor content is Mathlib's Lagrange theorem).

## Result

`Laplace/Multi/RadialTaylorBound.lean` (~170 lines), all gates green
with ZERO fix rounds — notable because the consult rated this tide
"High/API-sensitive". The flagged friction points dissolved:
iteratedDerivWithin_eq_iteratedDeriv takes ContDiffAt and works at
the Icc endpoint; taylor_within_apply is already the range-(n+1) sum
with (j!)⁻¹ smul coefficients, matching taylorHomogeneousTerm
through the ray identity with a one-line ring; gcongr closed the
final division monotonicity.

With `higherLaplaceDomainFamily_ofContDiff` the inverse Theorem 3.1
chain is HYPOTHESIS-COMPLETE from the note's prose data: global
smoothness + vanishing gradient + diagonal-matched posdef matrix →
package family → located_analytic_germ_recovery_of_ccData (analytic
at the minima, one C_c^∞ physical data premise, common region) →
p₁ = p₂ and germ equality.

### Suggested follow-ups

- Convenience end-to-end statement: compose
  higherLaplaceDomainFamily_ofContDiff with the located analytic
  capstone into one theorem whose hypotheses are only the bare-setup
  facts for the two centred losses (a ~40-line wrapper; optional,
  the pieces now compose in two lines at any call site).
- germbij.tex: markers for exists_taylorRemainder_bound /
  higherLaplaceDomainFamily_ofContDiff at thm:recovery + pin bump —
  GATED on user approval.
- The 27 recorded proof refactors (two review batches) remain
  available for a simplification tide.
