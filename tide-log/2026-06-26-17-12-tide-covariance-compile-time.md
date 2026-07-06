# Tide: Covariance.lean compile-time

**Direction (user):** I wish to make compilation time of Multi.Covariance.lean better in the Laplace seabed. Find a high impact change to make as a tide. Include before/after stats in the retrospective

**Seabed:** laplace, commit `0d09a7838e03f3bb666576beb5a5db851511831b`
**Started:** 2026-06-26

This is an engineering (compile-time) tide rather than a new-mathematics tide:
the "candidate" is a refactor verified by the build passing *identically*, not
a new lemma. Step 2's GPT-5.5 Pro consult is used as an adversarial review of
the proposed change (soundness + is there a higher-impact target) rather than
as candidate-selection.

## Seabed snapshot

`Laplace/Multi/Covariance.lean`: 3904 lines, one import (`Laplace.Multi.RescaledIntegrals`),
`set_option maxHeartbeats 800000`. 17 top-level declarations; the bulk is the
3600-line `AsymptoticIntegrals` section (lines 199–3799) holding ~12 large
`private lemma`/`theorem` proofs of integral bounds.

### Baseline profile (canonical clone, `lake env lean -Dprofiler=true`)

Whole-file build: **36.4 s wall / 108 s CPU**.

Profiler top sinks, in descending order:
- `nlinarith` (5 calls): **9.3 s + 5.7 s + 3.9 s + 2.7 s + 0.5 s ≈ 22 s** — over
  half the wall-clock build.
- `positivity` (`evalMul`) — 54 calls, individually 0.1–1.4 s, several hundred ms typical.
- `field_simp` — 20 calls, ~0.1–0.4 s each.
- `calc`-widget elaboration, `linarith` — many ~0.1 s each.

The `nlinarith` calls are by far the dominant single line item, and four of the
five are trivially replaceable without changing what is proven.

## Candidates v1 (Claude)

The four expensive `nlinarith` calls (the fifth, line 2860, is a small nested
`show t ≤ t^2 by nlinarith` at ~0.5 s, left as-is):

**A. Lines 1346 & 1927** — goal (after `rw`/`show`):
`c / 2 * ‖u‖ ^ 2 + c * Rφ ^ 2 / 2 * t ≤ c * ‖u‖ ^ 2`, with hypothesis
`h_half_le : c / 2 * (Rφ ^ 2 * t) ≤ c / 2 * ‖u‖ ^ 2`.
Treating `c * ‖u‖^2` and `c * Rφ^2 * t` as atoms, the goal reduces to exactly
`h_half_le` — purely linear. `nlinarith` is forming degree-2 products over the
large surrounding context for nothing.
→ replace `nlinarith [h_half_le]` with `linarith [h_half_le]`.

**B. Lines 2086 & 2421** — inside `h_norm_pow_le`, branch `1 < ‖u‖`, goal after
`rw [pow_succ]`: `‖u‖ ^ k ≤ ‖u‖ ^ k * ‖u‖`, with `hu : 1 < ‖u‖` and hint
`pow_nonneg (norm_nonneg u) k : 0 ≤ ‖u‖ ^ k`. This is the named lemma
`le_mul_of_one_le_right : 0 ≤ a → 1 ≤ b → a ≤ a * b`.
→ replace `nlinarith [pow_nonneg (norm_nonneg u) k]` with
`exact le_mul_of_one_le_right (pow_nonneg (norm_nonneg u) k) hu.le`.

Rationale: both eliminate `nlinarith`'s Positivstellensatz product search (which
scales badly with the number of in-context hypotheses, hence the 3–9 s costs)
and replace it with a single linear step / direct term application.

**C. Line 2860 (correction after measurement).** The fifth `nlinarith`
(`Real.sqrt_le_sqrt (show t ≤ t ^ 2 by nlinarith)`) was *mis-estimated* as the
cheap ~0.5 s one in v1. Re-profiling after edits A+B showed it actually costs
**3.9 s** — and it sits inside the single largest proof
(`abs_integral_remainder_mul_remainder_mul_rescaled_weight_le`, 598 lines), so
it is on the wall-clock critical path. `ht1 : 1 ≤ t` is in scope, so
`t ≤ t ^ 2` is exactly `le_self_pow₀ ht1 (by norm_num)`.
→ replace `show t ≤ t ^ 2 by nlinarith` with
`show t ≤ t ^ 2 from le_self_pow₀ ht1 (by norm_num)`.

## Numerical check

Not feasible (not a numerical statement): this is a compile-time refactor. The
soundness check is that the file builds *identically* — every downstream proof
still closes — which it does (only pre-existing `push_neg` deprecation warnings,
no errors). Candidate replacements were additionally pre-verified in a scratch
file (`le_mul_of_one_le_right`, `le_self_pow₀` close the exact goals).

## Result (timing)

All measurements: `lake env lean Laplace/Multi/Covariance.lean` in the tide
worktree, warm Mathlib cache, same machine.

| Metric            | Before | After  | Δ          |
|-------------------|--------|--------|------------|
| Wall clock        | 36.1 s | 28.4 s | −7.7 s (−21%) |
| CPU (user)        | 107 s  | 82 s   | −25 s (−23%)  |
| `nlinarith` calls | 5      | 0      | −5            |

Why CPU drops more than wall: Lean elaborates declarations across ~3 cores, so
the four `nlinarith` calls in *distinct* lemmas (A, B) were largely off the
critical path — removing them cut total work 18 s CPU but only ~3 s wall. The
fifth call (C), inside the largest single proof, *was* on the critical path:
fixing it alone gave the remaining ~4.5 s of wall reduction.

## GPT-5.5 Pro v1

Full response: `tide-log/gpt55_covariance-compile-time_v1.md`. Summary of verdict:

- **A, B, C all sound.** GPT confirmed `linarith` (the `c·Rφ²·t` monomial
  normalizes fine, no `ring` bridge needed), `le_mul_of_one_le_right` (correct
  current name, unifies over ℝ), and endorsed a term-mode replacement for C
  (my `le_self_pow₀ ht1 (by norm_num)` is equivalent and cleaner than GPT's
  `simpa [pow_two] using le_mul_of_one_le_right …`).
- **Key refinement: use `linarith only [h_half_le]`, not bare `linarith`.** The
  `only` stops the tactic scanning the whole (large) local context — "the
  important compile-time guard" for deep proofs. Applied. (Measured time
  unchanged here at 28.4 s — the post-`rw` context for these two goals is small
  enough that the scan wasn't the cost — but it is the more robust form and
  guards against future context growth.)
- **Targeting `nlinarith` is confirmed the highest-impact move.** GPT explicitly
  agreed (~22 s of ~36 s). Secondary advice, deferred: `maxHeartbeats` does not
  affect speed (only the give-up point); splitting the file helps incremental
  rebuilds/parallelism but not a single slow tactic; the 54 `positivity` calls
  are "probably not worth touching unless re-profiling shows them dominant."

## Vote

- Claude: the five-call `nlinarith` removal (Shapes A/B/C), with A using
  `linarith only`.
- GPT-5.5 Pro: same — endorsed the targets and contributed the `only` guard.

Agreed.

## Step 3 hand-off / Result

No separate `lean-formalisation` hand-off was needed — the change is a
mechanical 5-line tactic refactor, applied and verified directly. The file
builds with no errors (only pre-existing `push_neg` deprecation warnings) and
zero `nlinarith` calls remain. Final stats are the table above. Commit SHA:
recorded on merge.

Note: no LaTeX engine is installed in this environment, so the mandatory
`pdflatex` overfull-`\hbox` check on the retrospective could not be run here;
long Lean identifiers were placed in footnotes per the TeX-hygiene rule as a
precaution. The check should be run by the publish step / on a machine with
TeX.

## Retrospective

Retrospective: `lean/laplace/retrospectives/2026-06-26-17-12-tide-covariance-compile-time.tex`
