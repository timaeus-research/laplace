# Tide: germbij-analytic-corollary

**Direction (user):** continue the germbij arc (auto mode): the composed
corollary (candidate B of the previous tide's deliberation), the 1D
identifiability lower bound under analytic hypotheses outright, quantifiers
arranged constants-first then all sufficiently large t.

**Seabed:** laplace, main at 6aed3e6 (full germbij arc + the analytic
instantiation `analytic_growth_lower_bound`).
**Started:** 2026-08-09T03:25Z
**Worktree/branch:** laplace-tide-germbij-analytic-corollary /
tide/germbij-analytic-corollary (base verified 6aed3e6 after rebase onto
merged main)

## Deliberation (carried over)

Candidate B of the germbij-analytic tide, explicitly deliberated there and
deferred by joint vote ("B should be a short subsequent composition once A
is stable"; see `gpt55_germbij-analytic_v1.md` at 6aed3e6). A is now merged;
this tide executes the composition. No fresh consult.

## Candidate (statement)

```
theorem analytic_pencil_difference_lower_bound
    (L1 L2 psi : R -> R)
    (hL1a : AnalyticAt R L1 0) (hL2a : AnalyticAt R L2 0)
    (hne : analyticOrderAt (fun w => L2 w - L1 w) 0 <> top)
    (hL1 : forall w, 0 <= L1 w) (hL2 : forall w, 0 <= L2 w)
    {C0 R : R} (hC0 : 0 <= C0) (hR : 0 < R)
    (hsum : forall w in Icc 0 R, L1 w + L2 w <= C0 * w^2)
    (hpsi0 : forall w, 0 <= psi w) (hpsi1 : forall w in Icc 0 R, psi w = 1) :
    exists (m : N) (c r0 : R), 0 < c /\ 0 < r0 /\ r0 <= R /\
      forall t, 4 <= r0^2 * t ->
        (minorant integrable at t) -> (Fubini integrand integrable at t) ->
        (slices integrable at t) ->
        c * (t * t^(-(m:R) - 1/2))
          <= integral ((L2 - L1) psi) (e^{-tL1} - e^{-tL2})
```
Proof: apply `analytic_growth_lower_bound` to g = L2 - L1 (analytic by
`AnalyticAt.sub`), get (m, c0, r1, growth bound); set r0 := min r1 R and
c := c0^2 * exp(-(4*C0)); for each admissible t apply
`pencil_difference_lower_bound` with hypotheses restricted from Icc 0 R and
Icc 0 r1 to Icc 0 r0. The conclusion is literally the merged theorem's
conclusion at c0, so the final step is `exact`.

## Numerical check

Not feasible as a single number (existential constants); the underlying
inequality was checked in the identifiability tide (margin ~5.4e5). Shape
check: with L1 = w^2/2, L2 = w^2/2 + w^4: g = w^4 has analyticOrderAt = 4,
unit factor g = 1, so the instantiation yields m = 4, c0 = 1/2 (any c0 <
1), consistent with the earlier check's m = 4, c = 1.

## Vote

Carried over: both parties voted for exactly this composition as the
follow-up to the analytic instantiation ("B should be a short subsequent
composition once A is stable").

## Result

`Laplace/AnalyticIdentifiability.lean`, registered in `Laplace.lean`.
Declaration, sorry-free:
- `Laplace.analytic_pencil_difference_lower_bound`: for L1, L2 >= 0 analytic
  at 0 with differing germs, dominated by C0 w^2 on [0, R], and a bump psi,
  there exist m, c > 0, r0 in (0, R] such that for every t with
  4 <= r0^2 t (and the per-t integrability premises),
  c * t * t^(-(m:R) - 1/2) <= Delta_t((L2 - L1) psi).

One iteration: the first attempt forgot the merged 1D composite's window
ContinuousOn hypothesis; rather than adding it as a premise it is now
*discharged from analyticity* (AnalyticAt.eventually_analyticAt gives a
ball of analyticity; r0 is shrunk by rho/2; on the admissible window the
integrand is continuous via fun_prop from the pointwise ContinuousAt).
The corollary's premises are therefore exactly: analyticity, nonnegativity,
quadratic domination, the bump, and per-t integrability. Full `lake build`
passes; `scripts/sorries` 0/0/0/0.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-09-03-25-tide-germbij-analytic-corollary.tex
