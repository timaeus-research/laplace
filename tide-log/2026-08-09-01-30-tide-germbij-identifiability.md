# Tide: germbij-identifiability

**Direction (user):** third tide of the germbij chain (auto mode): compose the
pencil identity (tide germbij-pencil, merged 2f56d02), the comparison lemma,
and the sector bound (tide germbij-sector, PR #22) into the quantitative core
of germbij Theorem 7.3 in one dimension: the lower bound
`Delta_t(g psi) >= c^2 exp(-(4 C0)) * t * t^(-(m : R) - 1/2)` that contradicts
`o(t^{-infty})`.

**Seabed:** laplace, branch tide/germbij-sector (linear chain; contains
Pencil.lean and Sector.lean).
**Started:** 2026-08-09T01:30Z
**Worktree/branch:** laplace-tide-germbij-identifiability /
tide/germbij-identifiability (base tide/germbij-sector)

## Seabed snapshot

- `Laplace/Pencil.lean`: `exp_sub_exp_pencil`, `exp_pencil_identity`,
  `pencil_identity_integrated` (Fubini form, hypothesis: uncurried integrand
  integrable on `(volume.restrict (Ioc 0 1)).prod volume`), `exp_pencil_ge`
  (Boltzmann comparison along the pencil), `partitionFunction_pencil`.
- `Laplace/Sector.lean`: `sector_window_lower_bound`, `sector_lower_bound`
  (bound `c^2 * exp(-(4*C0)) * t^(-(m:R) - 1/2)` over
  `Icc ((sqrt t)^{-1}) (2*(sqrt t)^{-1})` under `4 <= r0^2 * t`).

## Deliberation (carried over)

This is candidate C of the germbij-pencil tide's deliberation, and step 7 of
GPT-5.6 Sol's proposed chain there ("apply the integrated pencil identity with
`phi = g * psi`, use nonnegativity to restrict to the good sector, then use
the pencil comparison and sector lemma"). Proceeding on that deliberation of
record; no fresh consult.

## Candidate (statement)

For `L1 L2 psi : R -> R`, `m : N`, `c C0 r0 t : R`, `g := fun w => L2 w - L1 w`:
hypotheses
- `hc : 0 <= c`, `hC0 : 0 <= C0`, `hr0 : 0 < r0`, `hrt : 4 <= r0^2 * t`,
- `hL1 : forall w, 0 <= L1 w`, `hL2 : forall w, 0 <= L2 w`,
- `hsum : forall w in Icc 0 r0, L1 w + L2 w <= C0 * w^2`,
- `hg : forall w in Icc 0 r0, c * w^m <= |g w|`,
- `hpsi0 : forall w, 0 <= psi w`, `hpsi1 : forall w in Icc 0 r0, psi w = 1`,
- continuity of `L1, L2, psi` (for the sector continuity and integrability),
- the Fubini integrability hypothesis of `pencil_identity_integrated` for
  `phi = fun w => g w * psi w`,
- integrability of the minorant and of each s-slice (derived or hypothesised).

Conclusion:
```
c^2 * Real.exp (-(4 * C0)) * (t * t^(-(m : R) - 1/2))
  <= integral (fun w => (g w * psi w) *
       (Real.exp (-(t * L1 w)) - Real.exp (-(t * L2 w))))
```

Chain: pencil identity with phi = g psi; integrand of the s-average is
g^2 psi e^{-t L_s} >= g^2 psi e^{-t(L1+L2)} pointwise (exp_pencil_ge);
inner-integral monotonicity (integral_mono_of_nonneg); the s-average of the
constant minorant is the minorant (interval length 1; interval integrability
of the s-slice function from the Fubini hypothesis via
Integrable.integral_prod_left); restrict the minorant integral to the window
Icc ((sqrt t)^{-1}) (2 (sqrt t)^{-1}) (nonneg integrand, setIntegral_le_integral),
where psi = 1 (window inside [0, r0] since 4 <= r0^2 t); finish with
sector_lower_bound applied to K = L1 + L2, a = g.

## Numerical check

Composite at t = 100, L1 = w^2/2 (restricted), L2 = w^2/2 + w^4, so
g = w^4 (m = 4, c = 1), L1 + L2 = w^2 + w^4 <= 2 w^2 on [0,1] (C0 = 2),
psi = 1 on [-1,1] cutoff: Delta = int_{-1}^{1} g (e^{-tL1} - e^{-tL2}) dw
computed by quadrature = 1.815e-05 >= bound c^2 exp(-8) * t^{1-4-1/2}
= 3.355e-11 (margin ~5.4e5; scipy). The hypothesis L1 + L2 <= 2 w^2 on [0,1]
verified numerically on a grid.

## Step 3 hand-off / Result

File: `Laplace/Identifiability.lean` (registered in `Laplace.lean`).
Declaration, sorry-free:
- `Laplace.pencil_difference_lower_bound`: under the germbij Theorem 7.3
  hypotheses (1D, analytic input factored as `c * w^m <= |L2 - L1|`), the
  observable `(L2 - L1) * psi` gives
  `c^2 * exp(-(4*C0)) * (t * t^(-(m:R) - 1/2)) <= Delta_t`.

Full `lake build` passes; `scripts/sorries` 0/0/0/0. Compiled on the second
attempt: the only failure was a `rw` that could not see through an unreduced
lambda application produced by `setIntegral_congr_fun` (fixed with
`simp only`, which beta-reduces first). Integrability hypotheses kept
explicit per the deliberated pattern: minorant integrable, uncurried pencil
integrand product-integrable (feeds both the Fubini step and, via
`Integrable.integral_prod_left` + `intervalIntegrable_iff`, the interval
integrability of the slice function), and per-slice integrability (could be
weakened to a.e.-s via `prod`-a.e. slicing; noted as a follow-up).

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-01-30-tide-germbij-identifiability.tex
