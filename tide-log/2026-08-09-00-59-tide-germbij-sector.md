# Tide: germbij-sector

**Direction (user):** continuation of the germbij formalisation chain (see the
germbij-pencil tide, merged as 2f56d02): the 1D sector lower bound, germbij
Lemma 7.2, toward the identifiability theorem (germbij Theorem 7.3). Auto mode.

**Seabed:** laplace, origin/main at the germbij-pencil merge (2f56d02),
which contains `Laplace/Pencil.lean`.
**Started:** 2026-08-09T00:59Z
**Worktree/branch:** laplace-tide-germbij-sector / tide/germbij-sector

## Seabed snapshot

As in the germbij-pencil tide log, plus the newly merged `Laplace/Pencil.lean`
(scalar/pointwise/integrated pencil identity, `exp_pencil_ge` comparison,
`partitionFunction_pencil`). The sector bound is the second ingredient of the
germbij Theorem 7.3 chain and is independent of the pencil file; it will be
consumed together with it by the composite tide.

## Deliberation (carried over from germbij-pencil, v1 consult)

This candidate was drafted and deliberated in the previous tide's Step 2
(candidate B there; see `tide-log/gpt55_germbij-pencil_v1.md` in the repo at
2f56d02). GPT-5.6 Sol's verdict on B, verbatim summary: statement and constant
`c^2 * exp(-(4*C0)) * t^(-m - 1/2)` correct; side condition `4 <= r0^2 * t`
sufficient (implies `t > 0` and `2 t^{-1/2} <= r0`); the hypotheses should be
stated as explicit pointwise bounds on `Set.Icc 0 r0` and the statement needs
measurability/continuity of `a` and `K` for the Lebesgue integral inequality;
`t^{-1/2}` should be `Real.sqrt`- or `rpow`-explicit. Its recommended
decomposition (steps 5-6 of its 7-step chain):

1. **Scale-window lemma.** On a window `[u, 2u]` with `0 < u`, `2*u <= r0`:
   from `0 <= K <= C0 * w^2` and `c * w^m <= |a w|` on `Icc 0 r0`,
   ```
   integral over Icc u (2*u) of (a w)^2 * exp (-(t * K w))
     >= u * (c^2 * u^(2*m)) * exp (-(4 * C0 * t * u^2))
   ```
   (constant lower bound times interval length; isolates set-integral
   monotonicity from the t-algebra).
2. **Laplace-scale corollary.** Substitute `u = t^(-1/2)` (as `Real.sqrt t`
   inverse or `t ^ (-(1/2) : R)`) under `4 <= r0^2 * t` to get
   ```
   integral over Icc (t^(-1/2)) (2*t^(-1/2)) of (a w)^2 * exp (-(t * K w))
     >= c^2 * exp (-(4 * C0)) * t^(-(m : R) - 1/2)
   ```

Per the tide skill's proceed-without-fresh-consult path (candidate already
deliberated, closed form numerically verified), we do not re-consult; the
prior consult is the deliberation of record.

## Vote

- Claude: candidate B via the two-step decomposition above.
- GPT-5.6 Sol (from the v1 consult of the previous tide): B is the natural
  next step after A1, with exactly this decomposition and the added
  measurability/continuity hypotheses.

Agreed candidate: B.

## Numerical check

From the previous tide's log: at t = 100, K = w^2 (C0 = 1), a = w^2
(m = 2, c = 1), r0 = 1: integral_{0.1}^{0.2} w^4 e^{-100 w^2} dw = 4.606e-06
>= e^{-4} * 100^{-2.5} = 1.832e-07 (margin ~25.1x, scipy quadrature).
Scale-window form at u = 0.1, t = 100: lower bound
u * c^2 * u^4 * exp(-4*1*100*0.01) = 0.1 * 1e-4 * e^{-4} = 1.832e-07, same
inequality.

## Step 3 hand-off

Target file: `Laplace/Sector.lean`. Statements as in the deliberation, with
hypotheses: `hK : forall w in Set.Icc 0 r0, 0 <= K w`, `hK2 : forall w in
Set.Icc 0 r0, K w <= C0 * w^2`, `ha : forall w in Set.Icc 0 r0, c * w^m <=
|a w|`, continuity of `a` and `K` on `Icc 0 r0` (for integrability),
`hu : 0 < u`, `hur : 2*u <= r0`; and for the corollary `hrt : 4 <= r0^2 * t`
with `u := (Real.sqrt t)⁻¹`.

## Result

`Laplace/Sector.lean`, registered in `Laplace.lean`. Declarations, sorry-free:
- `Laplace.sector_window_lower_bound` (window [u, 2u], constant lower bound
  times length)
- `Laplace.sector_lower_bound` (Laplace scale u = (sqrt t)^{-1}, bound
  c^2 exp(-(4 C0)) t^(-(m : R) - 1/2))

Full `lake build` passes; `scripts/sorries` reports 0/0/0/0. Surprises:
(i) the hypothesis `0 <= K` from the deliberation is not needed (only the
upper bound on K enters a lower bound on the Boltzmann factor); dropped.
(ii) The rpow/sqrt bookkeeping GPT warned about was real but contained:
`Real.sq_sqrt`, `inv_pow`, `pow_mul`, `Real.rpow_add/neg/natCast`,
`Real.sqrt_eq_rpow` cover it in a five-line chain. (iii) Compiled on the
first attempt modulo one deprecated tactic and the unused hypothesis.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-00-59-tide-germbij-sector.tex
