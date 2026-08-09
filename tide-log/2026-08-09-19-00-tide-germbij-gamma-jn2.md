# Tide: germbij-gamma-jn2 (stage 2a of the gamma-rung programme)

**Direction (user):** gamma-rung programme stage 2, first half: the
cubic-order remainder layer. (Stage 2 split at its natural seam during
execution: 2a = pointwise + integral remainder bounds at O(1/(t sqrt t));
2b = the quadratised decomposition and the second-order J_n headline.)

**Seabed:** laplace, main at 6e1ec45 (stage 1 merged: the signed
exponential remainder). Mirror source: the first-order remainder layer
of Laplace/OneD/IntegralRemainder.lean (pointwise -> combined ->
integral bound), with rescaled_max_decay reused verbatim.
**Worktree/branch:** laplace-tide-germbij-gamma-jn2 /
tide/germbij-gamma-jn2
**Started:** 2026-08-09T19:00Z

## Deliberation (programme-inherited)

The scoping consult (tide-log of stage 1, verbatim in that tide's
gpt56_gamma_rung_scoping_v1.md) specified this stage: the two-sided
remainder at order three composed with the existing two-branch decay,
the cube absorbed into even powers. Architectural choice made in
execution: error scale expressed as K / (t * Real.sqrt t) (rpow-free,
consistent with the seabed's 1/sqrt t style).

## Result

- Branch tide/germbij-gamma-jn2, Laplace/OneD/IntegralRemainder2.lean:
  perturbation_remainder3_pointwise, abs_pow_nine_le,
  rescaled_cube_bound, perturbation_remainder3_combined,
  integrable_pow_add3_mul_exp_neg_mul_sq,
  perturbation_remainder3_integral_bound.
- Six build iterations (heaviest of the programme so far): abs_add is
  now abs_add_le; gcongr discharges side conditions from context (two
  dead `exact`s); positivity needs even-power rewrites (x^{2k} ->
  (x^k)^2 shape) and cannot cube-sign an atom without its positivity in
  context; the conclusion-only implicit alpha needed explicit passing
  (the anchor lesson, again); a t*sqrt(t) <= t^3 needed staged nlinarith
  hints; one misfired heredoc edit hit a stray SRI-root Laplace.lean
  (untracked junk from an earlier session mishap, now deleted) instead
  of the worktree — caught by the failed lake build, canonical clone
  verified clean.
- Numerical check: not applicable to this half-stage (pure inequalities;
  the programme target was pinned at scoping; stage 2b's decomposition
  will carry the numerical check of the second-order coefficients).

## Next

Stage 2b: quadratised_integral_decomposition (six-term split, the
(sqrt t)-atom identity trick for s^2) and J_n_asymptotic_order2
(headline: main + A^2/(2t) m_{n+6}, error K/(t sqrt t)).
