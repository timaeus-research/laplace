# Tide: germbij forward programme, stage 3 (the forward domain)

**Direction (user):** the nondegenerate core, forward direction;
implementation order item 3 of the archived programme-A design
consult (in the stage-1 tide log).
**Seabed:** laplace, stacked on tide/germbij-forward-meso (PR #97,
unmerged at start).
**Started:** 2026-08-10T04:10 local

## Candidates (per the design consult, section B)

1. `ForwardExpansionDomain N`: the ONE-FIELD Peano mixin over
   HigherLaplaceDomain (N+2) — the little-o Taylor remainder at
   order N+2 through the degree-(N+2) sum (range (N+3)), which the
   O-bound cannot supply and which identifies the order-N
   coefficient.
2. `exponentTerm s = taylorHomogeneousTerm (s+2)` (the V_s), the
   zeroth-term identity T_0 = L 0 (definitional), and
   `scaledTaylorRemainder` (the remainder through degree N+2 divided
   by q^{N+2}) with its two lemmas: pointwise tendsto to 0 from the
   Peano field (composed along q -> q.z), and the window polynomial
   bound (the O-remainder through N+1 plus the operator-norm bound
   on the degree-(N+2) term).
3. `exponent_split`: for q > 0 and vanishing degree-1 term (the
   critical-point hypothesis, taken as a hypothesis pending the
   quadratic bridge the consult said to keep separate),
   (L(q.z) - L 0)/q^2 = T_2(z) + sum_{s=1}^N q^s V_s(z) +
   q^N * scaledTaylorRemainder q z — the exact split stage 4's
   graded exponential consumes. The T_2 = H/2-form bridge is
   deferred per the consult ("bridged separately").

## Vote

- Claude: as staged. - GPT-5.6 Sol: its own section B. Agreed.

## Numerical check

Not feasible: exact algebraic split over verified components.

## Result

Commit 133ebfd (pre-rebase; rebased onto main at cf92cbb after PR #97
merged). `Laplace/Multi/ForwardDomain.lean` (~250 lines):

- `ForwardExpansionDomain N L H` — one-field Peano mixin over
  `HigherLaplaceDomain (N+2)`.
- `exponentTerm`, `taylorHomogeneousTerm_zero`,
  `taylorHomogeneousTerm_zero_point`, `abs_taylorHomogeneousTerm_le`.
- `taylorRem` / `scaledRem` / `taylorRem_zero`,
  `tendsto_scaledRem` (pointwise vanishing from the Peano field),
  `remConst` / `abs_scaledRem_le` (uniform window bound),
  `exponent_split` (the exact identity, hypothesis
  `taylorHomogeneousTerm 1 L = 0`).

Surprises: the endgame helper for `R/q^(N+2) * q^N * q^2 = R` was
unnecessary — with both nonzeroness facts in context, `field_simp; ring`
closes the whole split (`ring` normalizes `q^(N+2) = q^N * q^2` with
variable `N`). One unused-simp-arg warning caught by the zero-warnings
gate; the `rw [hgrad]` beta-reduces on its own.

### Suggested follow-ups

- Stage 4 (ExpGraded): recursive `expCorrectionCoeff` P_j and the graded
  exponential expansion on the mesoscopic window, consuming
  `tendsto_scaledRem` + `abs_scaledRem_le`.
- Bridge `taylorHomogeneousTerm 2 L = (1/2) qform H` where the domain's
  Hessian data identifies them (deferred by design).
