# Tide: optimize-build-2

**Direction (user):** another round of /tide-optimize on laplace (same brief: wall time of the module build is the main metric, don't compromise too hard on code length, peak RAM matters; no GPT consults; short retrospective focused on changes and before/after).
**Seabed:** laplace, commit ff68d99 (tip of `tide/optimize-build`, PR #132, stacked)
**Started:** 2026-08-25T13:39Z

## Starting point

Round 1 (`2026-08-24-16-07-tide-optimize-build`) took the forced rebuild 402 → 137 s. Its final critical path (132 s) is the forward/recovery arc: Dilation → StdGaussian → QuadForm → RayRescale → QuadLowerBound 9.4 → RescaledDCT → HessianMoments → LocalRateDCT 7.7 → PairwiseRate → NormalizedRate → DegreeRecovery → CoeffFn → **ScalarBounds 16.0** → GaussAbsorb → **WindowMajorant 12.0** → NumeratorExpansion → NumeratorTails 6.6 → AsymptoticDivision → ForwardTheorems → Laplace → Solutions. The covariance chain (…→ CovarianceExplicit ~54 s) sits just below it. Six files were reverted to `import Mathlib` umbrellas after shake false positives (AsymptoticDivision, SeparableRecovery, SingularSmooth, AnharmonicFourthCumulant, LocalRateDCT, ScalarBounds).

## Plan

1. Re-record baseline (`lake build --no-cache`), confirm ~137 s and the path.
2. `-Dtrace.profiler` on ScalarBounds, WindowMajorant, QuadLowerBound, LocalRateDCT, NumeratorTails.
3. Fix hot tactics (use lean-state for goals/edit checks; full compiles only for timing).
4. Chain surgery where cheap: targeted imports for the reverted umbrella files on the path.
5. Gates: fingerprint, sorries, axioms, warnings; record after; retrospective.

## Measurements and changes (round 2)

**Baseline** (ff68d99, `lake build --no-cache`, lakefile artifact cache off): **137.9 s wall**, path 132.7 s = the forward/recovery chain (21 hops, most 4–7 s ≈ import floor + a little work; fat hops ScalarBounds 16.0, WindowMajorant 13.0, QuadLowerBound 9.6, LocalRateDCT 7.7).

**Attribution** (`-Dtrace.profiler`, threshold 1 s):
- ScalarBounds: entire 16.8 s is one line — `have hshift := (summable_nat_add_iff (N + 1)).mpr hsum` (16.36 s): higher-order unification inventing `f` from `fun i ↦ x^(i+(N+1))/…`. Fix: pass `(f := fun n : ℕ ↦ x ^ n / (n.factorial : ℝ))` explicitly → module 16.8 → 4.85 s standalone (≈ the import load).
- WindowMajorant (10 s decl `normalized_window_remainder_bound`): two context-taxed `nlinarith` → `nlinarith only [...]` (goals read via lean-state) → 13 → 9.4 s.
- QuadLowerBound/LocalRateDCT/NumeratorTails: diffuse (all decls ≤ 3.7 s).

**Edge cuts** (verified by name-usage grep + build): ScalarBounds imports ExpGraded instead of CoeffFn (uses nothing from CoeffFn); LocalRateDCT imports RescaledDCT instead of HessianMoments; GaussAbsorb imports ForwardDomain instead of ScalarBounds; WindowMajorant gains a direct CoeffFn import (uses `correctionCoeffFn`). Recorded rebuild → **131.1 s**; the critical path flipped back to the covariance chain (Covariance 26 → Sharp 28 → Explicit 52 = 126 s), whose head also shrank from round-1 import narrowing (Defs→GaussianIBP→RescaledIntegrals 27.8 → 12.3 s).

**Covariance monster** (`abs_integral_remainder_mul_remainder_mul_rescaled_weight_le`, 24.7 s): six `positivity` calls at ~1.4 s each — all on goals whose atoms are `set`-bound constants (Kφ', Kψ', Cφ, Cψ, M0, MN), so positivity scans the 60-hypothesis context per atom. First replaced with explicit `mul_nonneg`/`div_nonneg` terms (26 → 17.6 s) — then, on review ("fairly ugly"), swapped for a single `clear_value M4 M0 MN Kφ' Kψ'` after their `_nn` facts with the original `positivity` calls kept: 22.9 → 19.0 s standalone, full rebuild 127.6 s (vs 126.5 with the terms). No `positivity only` exists; `positivity [h]` only adds hypotheses. Recorded rebuild → **126.5 s**, path = forward chain again at 122.6 s.

**Import-floor pass**: 20 of the forward chain's modules still had `import Mathlib` (load 4.4 s vs ~2.5 s for a targeted set). `#min_imports` (via lean-state `check` on a temporary trailing `#min_imports`) showed that for 15 of them the umbrella is fully redundant given their Laplace imports, and gave 1–4 targeted modules for the other 5. Applied in chain order; validating with a per-module `lake build --no-cache` walk that re-derives imports against the freshly narrowed upstream on failure (falling back to restoring the umbrella).

Process note (per feedback after round 1): goals and per-edit checks via `lean-state`; `lake env lean`/`lake build --no-cache` only for timing. One slip: a text-based replace matched an earlier lemma with an identical `have` line — reverted the file and redid edits by line number, bottom-up.

## Final numbers

Import-floor pass verified: all 20 chain modules built with narrowed imports on the first try (15 umbrellas dropped outright, 5 replaced by 1–4 targeted modules); full rebuild green. The path flipped back to the covariance chain: Defs 3.5 → GaussianIBP 3.4 → RescaledIntegrals 5.3 → Covariance 21 → CovarianceSharp 29 → CovarianceExplicit 52 → Laplace → Solutions = 122.3 s; the forward chain is now below it.

**Round 2: 137.9 → 127.6 s wall** (−7.5%; 126.5 with the explicit positivity terms); CPU 910 → 882 s; simulated 8-core 162 → 155 s, 16-core 131 → 125 s. Cumulative over both rounds: 402 → 127.6 s (−68%).

## Result

Gates: fingerprint byte-identical (1096 public signatures); warning set identical modulo line shifts (432 lines); `scripts/sorries` 0/0/0/0; `#print axioms gibbsCov_first_order_rate_explicit` = [propext, Classical.choice, Quot.sound]. Commit: the single commit on `tide/optimize-build-2` (stacked on `tide/optimize-build`, PR #132).

**Remaining headroom** (all need proof restructuring, deferred): the three covariance monoliths — CovarianceSharp's `abs_integral_corrected_bracket_centered_bilinear_le` (27 s: three 2 s `field_simp` on `funext` identities plus diffuse steps), Covariance's remainder×remainder bound (~13 s of work left), and CovarianceExplicit's five ~33 s tails (87 plain `linarith` sites at ~8 s each tail, `field_simp` chains). Hoisting their `have hpt` pointwise bounds into `private` lemmas is the mechanical option.

## Retrospective

Retrospective: laplace/retrospectives/2026-08-25-13-39-tide-optimize-build-2.tex
