# Tide: germbij multivariate H4 (dominated convergence)

**Direction (user):** standing auto-mode commission on the germbij
note; stage H4 per the archived H3/H4 shape consult (in the H3a
tide's log dir).
**Seabed:** laplace, branch tide/germbij-multi-peano at 8bb34e5
(stacked on unmerged H3b; H3a+H3b in PRs #69-#70, chained watcher).
**Started:** 2026-08-09T08:40 local

## Candidates

Fixed by the consult's "Tide H4" section:

1. **Dominator integrability**: Integrable ((1 + ‖x‖²)·e^{-c‖x‖²})
   for c > 0, by the elementary bound t² ≤ (2/c)e^{ct²/2} (from
   u + 1 ≤ e^u), reducing to the H2a norm-Gaussian lemma at c/2 and
   c. No dilation transport needed.
2. **`LocalLaplaceDomain` structure** extending `LocalQuadraticApprox`
   with the integration domain: U, measurability, δ with
   ball δ ⊆ U, the H4-facing rescaled lower bound field
   (c, c_pos, rescaled_lower : 0 < q → q•x ∈ U → c‖x‖² ≤ quotient —
   the consult's "even cleaner" option, so U ⊆ closedBall need not
   be exposed), and measurable_L.
3. **The generic theorem** (one DCT, not three): for continuous h
   with |h x| ≤ C(1 + ‖x‖²),
   Tendsto (fun q ↦ ∫ x, indicator {x | q•x ∈ U}
     (fun x ↦ h x · exp(-(L(q•x) - L 0)/q²)) x) (𝓝[>] 0)
     (𝓝 (∫ x, h x · quadKernel H x)).
   Pointwise: q•x → 0 ∈ ball δ ⊆ U eventually, rescaled_tendsto +
   continuity of exp. Domination: rescaled_lower gives
   exp ≤ e^{-c‖x‖²} on the indicator support.
   DCT: tendsto_integral_filter_of_dominated_convergence.
4. **Corollaries** at h = 1, x_i, x_i·x_j (coordinate bounds
   |x_i| ≤ ‖x‖, |x_i x_j| ≤ ‖x‖² fit the growth hypothesis), with
   the limits rewritten to the H2 values (Z_H, 0,
   jacInv·Z₀·H⁻¹_{ij}).

## Numerical check

The limit targets are exactly the H2 integrals verified numerically
in the H2a tide log (d=2, 8 decimals); the convergence statement
itself is structural (Tendsto). No new closed form.

## Vote

- Claude: as staged (the consult's own H4 section).
- GPT-5.6 Sol: same (archived).

Agreed.
