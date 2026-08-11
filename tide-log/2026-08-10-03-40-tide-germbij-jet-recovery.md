# Tide: germbij-jet-recovery (weighted-jet programme, stages 3D-3G)

**Direction (user):** the programme's closing tide (auto mode,
standing delegation): quotient-difference lemma (3D), one-rung
recovery via variance positivity at s = 2k+r (3E), finite strong
induction over rungs (3F), and transfer back to t-data through the
stage-2 scaling identity (3G) — ending at the germbij §7.4 comparison
recovery theorem: two enveloped jets with eventually-equal Gibbs
moment data have equal coefficients.

**Seabed:** laplace, stacked on tide/germbij-jet-difference (PR #55,
in CI at tide start). Linear-chain worktree.
**Worktree/branch:** laplace-tide-germbij-jet-recovery /
tide/germbij-jet-recovery
**Started:** 2026-08-10T03:40Z

## Deliberation

No fresh consult: stages 3D-3G were specified, with proof sketches
and the failure-point analysis, in the route consult archived at
tide-log/gpt56_jet_difference_route_v1.md (sections "Stage 3D" to
"Stage 3G" and the quotient-difference lemma statement). This is the
documented prior-deliberation path. One addition beyond the consult's
list, forced by the Lean proof of 3D/3E: the base-point limit
J_s(q) → A_s as q → 0⁺ (the consult implicitly assumed it; it is a
second, simpler application of the same DCT pattern as 3C).

## Vote

- Claude: stages 3D-3G as one closing tide, with the base-point
  limit lemma added.
- GPT-5.6 Sol (route consult, verbatim): "Once the unnormalized
  limit is available, the covariance quotient and strong induction
  should be comparatively routine."

Agreed (carried over).

## Numerical check

The end-to-end content was checked across the two previous tides'
executed checks: the covariance limit -(c1_r - c2_r) Cov(u^s, u^{2k+r})
(ratios 0.9999 at q = 0.005, parity vanishing at s = 2), and the
variance positivity/Gamma forms (6-decimal agreement, k in {1,2},
j = 1..4). The new stages are identity-level bookkeeping over those
limits; the one new analytic fact (J_s(q) → A_s) is a special case of
the checked scaling identity at c1 = c2. No new check required.

## Incident: the previous tide's build gate was vacuous

Discovered at this tide's first build: the 3A-3C tide never added
`import Laplace.OneD.JetDifference` to Laplace.lean, so its
`lake build` (and PR #55's CI) never compiled JetDifference.lean at
all. The previous tide log and retrospective claim a clean build with
zero warnings; that claim was FALSE — the file had ~15 errors of the
usual first-build classes (renames, beta-unreduced congr goals,
implicit-argument inference, dead tactics), all caught and fixed in
this tide. PR #55 merged an uncompiled file. Root cause: the build
gate silently passes when the new file is not in the import closure;
the job-count difference is too noisy to notice. New protocol
(promoted to CLAUDE.md): after adding a file, verify BOTH the import
line in Laplace.lean AND the new .olean in .lake/build before
claiming a build. An erratum is appended to the 3A-3C retrospective
in this branch.

## Result

- Declarations (Laplace/OneD/JetRecovery.lean, ~350 lines, zero
  sorries, zero warnings — this time verified via import + olean):
  jet_integral_tendsto (base-point DCT limit),
  quotient_difference_tendsto (3D, generic over any filter, with the
  σ = 0 division-convention case handled),
  jet_reference_variance_pos (bridge from stage 1 at t = a·(2k)!),
  jet_one_rung_recovery (3E), jet_recovery (3F, strong induction),
  polynomialJet_recovery (3G: eventual equality of Gibbs moments at
  x^{2k+r}, r = 1..R, as t → ∞ forces c₁ = c₂) — the germbij §7.4
  comparison recovery theorem, sorry-free end to end.
- Also repaired in this tide: JetDifference.lean (see incident) and
  the missing imports for both files.
- Surprises beyond the incident: (1) `set` folds existing occurrences
  only — hypotheses created later (e.g. by applying a lemma) arrive
  with raw unfolded terms, so fold them explicitly with rw [← h_def];
  (2) Tendsto.congr produces beta-unreduced lambda applications;
  funext-then-rwa on the function equality avoids the whole class;
  (3) div_eq_zero_iff.mp + resolve_right is the clean way to clear a
  positive denominator from an equation-to-zero.
