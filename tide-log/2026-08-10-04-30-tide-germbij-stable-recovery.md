# Tide: germbij-stable-recovery (programme C, stage C1)

**Direction (user):** the asymptotically stable recovery interface
(auto mode, standing delegation): variable-base jet recovery from
Tendsto-to-zero data at the coefficient-sensitive scales, with no
exact-equality hypotheses anywhere — the bridge the smooth-germ
programme needs, since Taylor replacement produces order-controlled
errors, never equal data.

**Seabed:** laplace, stacked on tide/germbij-lambda-package (PR #59
in CI at tide start). Linear-chain worktree.
**Worktree/branch:** laplace-tide-germbij-stable-recovery /
tide/germbij-stable-recovery
**Started:** 2026-08-10T04:30Z

## Deliberation

No fresh consult: C1 is specified in the programme scoping consult
(tide-log/gpt56_general_order_scoping_v1.md): "Replace exact eventual
equality by vanishing at the coefficient-sensitive scale. ... The
existing proof should adapt — its contradiction only needs the
observed difference to vanish at the relevant scale — but this
deserves its own theorem interface." Seabed survey confirms the
adaptation is small: jet_recovery (3F) ALREADY takes Tendsto data
((F₁−F₂)/q^{r} → 0 per rung), and base_recovery_of_tendsto is the
stable base interface; what is missing is only the combined
variable-base stable theorem. Documented prior-deliberation path.

## Vote

- Claude: one small tide, jet_recovery_stable (variable-base,
  all-Tendsto data).
- GPT-5.6 Sol (scoping consult): C1 as its own theorem interface.

Agreed (carried over).

## Numerical check

Not feasible as a distinct check: the statement is an interface
weakening of already-checked theorems (the covariance-limit and
second-moment checks of the two previous tides cover the analytic
content; C1 adds no new closed form). Noted per protocol.

## Result

- Theorems (Laplace/OneD/StableRecovery.lean, ~70 lines, zero
  sorries, zero warnings; gate verified via import + .olean):
  jet_recovery_stable (variable-base recovery from pure Tendsto data
  — second-moment difference → 0 and per-rung scaled differences → 0)
  and nondegenerateJet_recovery_stable (the k = 1, λ/2 interface the
  smooth-loss reduction will consume). First-try clean build.
- The tide confirms the scoping consult's prediction at the strongest
  reading: the "adaptation" was pure composition, because the
  programme's internal theorems were already limit-based; only the
  outermost packaging had hardened to eventual equality. Interface
  discipline (keeping _of_tendsto forms alongside equality forms)
  paid off exactly here.
