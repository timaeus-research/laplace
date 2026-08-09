# Tide: germbij multivariate H5 (normalization and covariance)

**Direction (user):** standing auto-mode commission on the germbij
note; stage H5 per the archived multivariate scoping consult.
**Seabed:** laplace, branch tide/germbij-multi-domconv at 874033d
(stacked on unmerged H4, PR #71).
**Started:** 2026-08-09T09:00 local

## Candidates

Per the scoping consult's Stage H5 ("cancel the common
q^d·e^{-L(0)/q²} factors and divide by the zeroth moment; the
first-moment limit is needed — covariance is not automatically the
raw second moment"):

1. `posteriorIntegral f q := ∫ 1_U(w)·f(w)·e^{-L(w)/q²} dw` and the
   **dilation identity** (exact, per q > 0):
   posteriorIntegral f q = q^d·e^{-L(0)/q²}·∫ A.integrand (f∘(q•)) —
   via `integral_dilation`, the indicator-preimage step, and the
   exponent split e^{-L(qx)/q²} = e^{-L0/q²}·e^{-(L(qx)-L0)/q²}.
2. Specializations pulling out q-powers: f = 1, w_i (factor q),
   w_i·w_j (factor q²), all landing on H4's `A.integrand` at the
   observables 1, x_i, x_i·x_j.
3. **Exact normalized identities** on the eventual set where the
   zeroth integrand integral is positive (guaranteed by its H4 limit
   jacInv·Z₀ > 0): q^{-1}E_q[w_i] = I_i(q)/I₀(q),
   q^{-2}E_q[w_iw_j] = I_ij(q)/I₀(q) — prefactors cancel exactly,
   no asymptotics.
4. **The three limits**: q^{-1}E_q[w_i] → 0,
   q^{-2}E_q[w_iw_j] → H⁻¹_{ij} (Tendsto.div with nonzero limit
   jacInv·Z₀), and q^{-2}Cov_q(w_i,w_j) → H⁻¹_{ij}
   (Tendsto.sub + mul against the vanishing first moments).

## Numerical check

The three limits are ratios of the H2 integrals verified numerically
in the H2a tide log (second moments / Z = H⁻¹ entries to 8 decimals
at d=2). The cancellation identities are exact algebra. No new
closed form.

## Vote

- Claude: as staged (the scoping consult's own H5 brief).
- GPT-5.6 Sol: same (archived).

Agreed.
