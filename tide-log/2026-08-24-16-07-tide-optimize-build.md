# Tide: optimize-build

**Direction (user):** tide-optimize on laplace — refactor the code to improve compilation times. Wall time of this module's build is the main metric (packages irrelevant); don't compromise too hard on code length; peak RAM matters (sum over concurrent lean processes). No GPT consults; shorter retrospective focused on what changed and before/after build performance.
**Seabed:** laplace, commit 0224a74
**Started:** 2026-08-24T16:07Z

## Context

A tactic-squeeze pass ran earlier today (2026-08-24) on a test branch (`chore/tactic-squeeze`, disregarded per user) and found closing-tactic replacements are worth only ~1% here. The known dominant cost from that session's profiling: `Laplace/Multi/CovarianceExplicit.lean` (~19.4k lines, ~296 s, ~72% of the critical path) — elaboration-bound, not closing-tactic-bound. This tide targets the build structurally: lakeprof critical path + simulated core scaling, then `-Dtrace.profiler` inside hot modules.

## Plan

1. Warm build in the worktree (artifact cache on) to warm page cache.
2. Flip `enableArtifactCache` off, force-rebuild own modules under `lakeprof record` → baseline.
3. `lakeprof report -p -s -a` → critical path and parallelism ceiling.
4. `-Dtrace.profiler` on the hot modules → per-declaration attribution.
5. Rewrite (split files / split declarations / cheapen hot tactics), gated per commit on: green build, public-signature fingerprint byte-identical, `scripts/sorries` clean.
6. Re-record, retrospective with before/after numbers.

## Measurements and changes

**Baseline (main, 0224a74)**: forced rebuild of own modules (packages cached, artifact cache off, page cache warm): **402 s wall, 1215 s CPU**, flat beyond 16 simulated cores. Critical path (98% of wall): Defs 6.0 → Basic 4.4 → QuadraticApprox 4.2 → GaussianIBP 5.8 → RescaledIntegrals 7.9 → Covariance 32.0 → CovarianceSharp 35.0 → **CovarianceExplicit 299.0** → Laplace 3.6 → Solutions 4.5.

**Attribution** (`-Dtrace.profiler` on CovarianceExplicit): `Elab.async` is on, so module wall ≈ serial frontend (15.4 s, measured via `debug.byAsSorry`) + longest proof tails. One proof, `abs_bulkErr_local_le`, cost ~323 s CPU: five sequential `h_piece` blocks each containing a `nlinarith [tiny hints]` on a trivial goal (`√t·t ≤ t²`, `1·t ≤ t²·1`, ...) — each ~65 s because default `nlinarith` preprocesses the entire (huge) local context and forms pairwise products. Same pattern at smaller scale across ~15 more lemmas (`abs_bulkErr_tail_le` 133 s, `expNumErr₄_bound` 91 s, ...).

**Changes** (all in `Laplace/Multi/CovarianceExplicit.lean`):
1. All 34 hinted `nlinarith [...]` → `nlinarith only [...]`. Only 2 sites needed an extra context fact added to the hint list (`hsqrt_inv_le`, `h_norm_pow`). Effect: `abs_bulkErr_local_le` 323→55 s, module 299→88 s (profiled).
2. The 2 hot bare `nlinarith` in `expNumErr₄_bound` → `nlinarith only` with explicit hint sets.
3. 20 `linarith` (incl. `linarith [hints]`) inside `abs_bulkErr_local_le` → `linarith only [...]` with per-site hypothesis lists (the piece-final combiners are formulaic: `[h_step, h_eq, h_final]`). Effect: 54→36 s.

**Result**: CovarianceExplicit standalone 54.4 s wall (vs ~299 s), peak RSS ~9.3 GB (unchanged; the cost was search time, not memory). Wall is now frontend (15 s) + a plateau of five ~34 s diffuse tails (`local_le`, `tail_le`, `FQQ`, `poly4`, `expNumErr₄` — big `calc`/`have` chains, no single hot tactic). Mid-tide full rebuild: 192 s.

**Gates**: public-signature fingerprint byte-identical (1096 signatures, `scripts/fingerprint.py`, sorted so file-split-insensitive); warning set identical (16 distinct warnings before and after); `scripts/sorries`: 0/0/0/0.

**Not pursued** (diminishing returns / out of scope):
- Splitting the file or de-privatizing helpers for cross-file parallelism — would change the public surface, violating the statement-invariance gate.
- Hoisting `have hpt` sub-proofs out of the Covariance (27 s) / CovarianceSharp (30 s) monsters: est. ~10-12 s combined, invasive restructuring of landed proofs.
- Narrowing `import Mathlib` (4.6 s load per chain module, 8 hops): est. ~12-16 s, fiddly per-file import surgery.
- Repo-wide nlinarith-only sweep off the critical path: no wall effect (build is parallelism-bound, flat ≥16 cores).

## Act 2: import narrowing (shake)

With the covariance chain tamed (177 s), the critical path became a 24-hop chain of small modules (forward/recovery arc), each paying ~4.6 s of full-Mathlib olean loading per hop. `lake exe shake --fix` rewrote 55 files (30 `import Mathlib` umbrellas → targeted lists; several intra-repo edges cut with compensating direct imports downstream). Shake false positives: 8 files broke (notation `∫` in Gibbs, `iteratedFDeriv` in RadialTaylor, transitive-name losses in AsymptoticDivision/SeparableRecovery/SingularSmooth/AnharmonicFourthCumulant/LocalRateDCT/ScalarBounds, plus paired-edit interactions in GaussAbsorb/AnharmonicCumulantsLogPartition). Repairs: re-add the needed import where identifiable, otherwise restore the file's original imports; all pinned in `scripts/noshake.json` (`ignore`/`ignoreAll`).

Gotchas for future optimize tides:
- `lake build` "Fetched" results after edits can mask breakage/measurements: the toolchain-level content-addressed store (`~/.elan/toolchains/<tc>/lake/cache/artifacts`) serves identical-content artifacts across trees. `lake build --no-cache` forces honest builds.
- Never build the canonical clone and a worktree concurrently — shared hardlinked package trees.
- Reverting one file of a shake edit-pair (cut edge upstream + compensating import downstream) re-breaks the other side; revert or repair pairs together.
- Dep-package oleans may exist only as cache blobs; materialize via each module's `.trace` (`outputs.o[0]`) hardlinked from the toolchain cache when a tool (shake, importModules) needs plain files.

## Final numbers

Full forced rebuild: **402 → 137 s wall** (−66%); CPU 1215 → 905 s; simulated 8-core 422 → 161 s. Final critical path (132 s): forward/recovery arc ending ScalarBounds (16 s) → GaussAbsorb → WindowMajorant (12 s) → … → Solutions; the covariance chain now sits just below it.

## Result

Gates at final state: fingerprint byte-identical (1096 public signatures); `scripts/sorries` 0/0/0/0; `#print axioms gibbsCov_first_order_rate_explicit` = [propext, Classical.choice, Quot.sound]; warning-set diff vs baseline: see below. Commit: the single commit on `tide/optimize-build` (this file is committed with it).

## Retrospective

Retrospective: laplace/retrospectives/2026-08-24-16-07-tide-optimize-build.tex

## Addendum (2026-08-25)

Two small edits ported from a second-round pass (whose other changes were dropped): in `Multi/WindowMajorant.lean` two context-taxed `nlinarith` → `nlinarith only [...]` (module 13 → 9.3 s); in `Multi/Covariance.lean` one `clear_value M4 M0 MN Kφ' Kψ'` after their nonnegativity facts, so the six `positivity` calls in `abs_integral_remainder_mul_remainder_mul_rescaled_weight_le` stop `isDefEq`-unfolding integral bodies while scanning the context (module 26 → ~21 s). There is no `positivity only`; `positivity [h]` only adds hypotheses.
