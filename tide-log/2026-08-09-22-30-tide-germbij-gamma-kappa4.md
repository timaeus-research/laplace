# Tide: germbij-gamma-kappa4 (stages 4-5 of the gamma-rung programme)

**Direction (user):** gamma-rung programme stages 4-5: the fourth
cumulant's limit, t^3 kappa4 -> 3 alpha^2/lam^5 - gamma/lam^4, over the
stage-3 moment rates.

**Seabed:** laplace, main with stage 3 merged (the three moment rates +
mean_anharmonic_asymptotic and mean_anharmonic_O2_rate).
**Worktree/branch:** laplace-tide-germbij-gamma-kappa4 /
tide/germbij-gamma-kappa4
**Started:** 2026-08-09T22:30Z

## Deliberation (programme-inherited) and assembly algebra

The scoping consult's 1(c) table verified the target
108A^2 - 24B (after lam^-2) = 3 alpha^2/lam^5 - gamma/lam^4; the
end value was numerically pinned at scoping (mpmath: -0.185837 at
(1.3, 0.4, 0.9)). Assembly identity (checked by hand, ring-provable):
t^3 kappa4 = t(t^2 mu4 - 3/lam^2) - 3 t((t mu2)^2 - 1/lam^2)
  - 4 (t^2 mu3)(t mu1) + 12 (t mu2)(t mu1)^2 - 6 (t mu1)^4 / t.
Limits: t(t^2 mu4 - 3/lam^2) -> C4 (squeeze from the stage-3 rate);
t((t mu2)^2 - 1/lam^2) = t(t mu2 - 1/lam)(t mu2 + 1/lam) ->
C2 * 2/lam; t^2 mu3 -> -15A/sl^3; t mu1 -> -alpha/(2 lam^2)
(seabed mean_anharmonic_asymptotic); last term -> 0. Total:
C4 - 6C2/lam - 180A^2/lam^2 + 108A^2/lam^2 = 108A^2/lam^2 - 24B/lam^2
= 3 alpha^2/lam^5 - gamma/lam^4 (constants by sl-atom + field_simp).

## Numerical check

The end value was pinned at programme scoping (archived in the stage-1
tide log); the intermediate coefficients C2, C4 were confirmed at
stage 3. No new quantities to check at this stage (pure limit algebra).

## Result

- Branch tide/germbij-gamma-kappa4, Laplace/OneD/Kappa4Asymptotic.lean:
  two private squeeze converters (order-2 rate -> t(f-L) -> C limit;
  sqrt-rate -> plain limit) and kappa4_anharmonic_asymptotic:
  t^3 (mu4 - 4 mu3 mu1 - 3 mu2^2 + 12 mu2 mu1^2 - 6 mu1^4) ->
  3 alpha^2/lam^5 - gamma/lam^4. The five piece limits (L4a, P1 via the
  difference-of-squares factoring, L3*L1, L2*L1^2, L1^4/t -> 0) combine
  by Tendsto algebra; the assembly identity is one ring; the constant
  evaluation is the sl-atom substitution.
- Six build iterations, all catalogue classes: squeeze_zero_norm' takes
  positional args (no named g); Real.sqrt_atTop is
  Real.tendsto_sqrt_atTop; two dead rings; a field_simp needing its
  ne-hypothesis plus a live ring; and tendsto_const_nhds needing the
  type-ascribed anchor (the catalogue's own entry).
- The t^{-2} Gaussian cancellation (3/lam^2 between mu4 and 3 mu2^2)
  happens structurally in the split, exactly as the scoping table
  predicted.
