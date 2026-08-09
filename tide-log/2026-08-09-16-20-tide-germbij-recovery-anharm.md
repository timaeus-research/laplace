# Tide: germbij-recovery-anharm

**Direction (user):** continue the germbij formalisation (auto mode):
first certified instance of the note's Theorem 3.1 (jet recovery at a
nondegenerate minimum): the recovery reading of the seabed's anharmonic
susceptibility asymptotics. Eventual equality of the mean and covariance
susceptibilities forces lambda and alpha equal: the triangular
induction's first two rungs.

**Seabed:** laplace, main at e826e0d. Consumes
gibbsExp_deriv_anharmonic_asymptotic (limit -1/lambda) and
gibbsCov_deriv_anharmonic_asymptotic (limit alpha/lambda^3), both from
the Stage-2 anharmonic programme.
**Worktree/branch:** laplace-tide-germbij-recovery-anharm /
tide/germbij-recovery-anharm
**Started:** 2026-08-09T16:20Z

## Candidate v1 (Claude)

Single theorem anharmonic_susceptibility_recovery: for two triples
(lambda_i, alpha_i, gamma_i) with the standard hypotheses (positivity,
discriminant), if the mean susceptibilities agree eventually and the
rescaled covariance susceptibilities agree eventually, then
lambda_1 = lambda_2 and alpha_1 = alpha_2. Proof: Tendsto.congr' +
tendsto_nhds_unique twice, then -1/l injectivity and alpha/l^3
extraction. gamma is not recovered at this order (next cumulant's
asymptotic, absent from the seabed) — the docstring states this as the
next rung.

## Numerical check

Not feasible in an informative way (uniqueness-of-limits packaging over
already-verified seabed limits; the underlying asymptotics were
numerically checked when Stage 2 landed).

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_recovery_anharm_v1.md`.
Summary: two separate EventuallyEq hypotheses confirmed as the right
packaging (a pair hypothesis is equivalent but less convenient for
callers); opaque treatment of F, G through congr' + tendsto_nhds_unique
confirmed sound; field_simp-based extraction endorsed; tide-sized.

## Vote

- Claude: single theorem in Laplace/OneD/RecoveryAnharmonic.lean.
- GPT-5.6 Sol: same. Agreed.

## Result

- Branch tide/germbij-recovery-anharm,
  Laplace/OneD/RecoveryAnharmonic.lean:
  anharmonic_susceptibility_recovery.
- FIRST-ATTEMPT CLEAN BUILD (the thread's second, after the multivariate
  turnkey): the tendsto_nhds_unique pattern is now fully routinized.
- Surprise: none. The two Stage-2 limits were consumed as opaque data
  exactly as deliberated. gamma recovery (the next rung) needs the
  fourth-cumulant asymptotic, recorded as the seabed's natural next
  Stage-2 extension.
