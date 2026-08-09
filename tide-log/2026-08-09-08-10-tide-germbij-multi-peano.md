# Tide: germbij multivariate H3b (uniform Peano + coercivity)

**Direction (user):** standing auto-mode commission on the germbij
note; stage H3b, the H3/H4 consult's flagged hardest step.
**Seabed:** laplace, branch tide/germbij-multi-rescale at 23ed5be
(stacked on unmerged H3a; consult archived in that tide's log dir as
tide-log/gpt56_h3_shape_v1.md).
**Started:** 2026-08-09T08:10 local

## Candidates

Fixed by the archived H3/H4 shape consult (section "Tide H3b"):

1. **Coercivity**: H.PosDef → ∃ λ > 0, ∀ x, λ‖x‖² ≤ qform H x.
   Route: sphere compactness (min of the continuous qform on the
   unit sphere, positive by PosDef; extend by the homogeneity
   qform H (c•x) = c²·qform H x), NOT spectral theory — the consult
   explicitly warns the smallest-eigenvalue route is a detour.
2. **Uniform quadratic Peano**: for C² L with fderiv L 0 = 0,
   (fun y ↦ L y - L 0 - qform (hessianMatrix L) y / 2) =o[𝓝 0]
   (fun y ↦ ‖y‖²).
   Route (consult section 2): segmentwise 1D Lagrange remainder —
   g(t) = L(t•y) on [0,1] gives L y - L 0 = g''(ξ)/2 with
   g''(ξ) = D²L(ξ•y)[y,y]; continuity of the second derivative at 0
   (ε-δ) bounds |D²L(w) - D²L(0)|_op ≤ ε on a ball, and
   le_opNorm₂ converts to ε‖y‖². Requires generalizing H3a's
   ray second derivative from base point 0 to arbitrary base points.
3. **Local lower bound**: ∃ δ c > 0: 0 < q → ‖q•x‖ ≤ δ →
   c‖x‖² ≤ (L(q•x) - L 0)/q², from 1 + 2 with ε = λ/2.
4. **Package**: structure `LocalQuadraticApprox L H` (fields
   hH_posDef, lambda, lambda_pos, qform_lower, quadratic_peano) with
   a `.ofContDiff` constructor and derived rescaled_tendsto +
   exists_local_lower_bound, exactly the interface H4 consumes.

## Numerical check

The H3a check (same log arc) already verified both targets
numerically: the quotient limit and the coercivity inequality
lambda_min·|x|² = 1.864 ≤ qform = 1.891 at the test point. No new
closed form appears in this tide.

## Vote

- Claude: as staged (the consult's own H3b section).
- GPT-5.6 Sol: same (archived).

Agreed.
