# Tide: germbij thm:singular composition, part 3 (smooth observable class)

**Direction (user):** Continuation of the user-approved (2026-08-10)
closing of the thm:singular composition gap. Parts 1-2 (PRs #120,
#121) delivered the prep lemmas and the point/locus theorems with the
family premise over CONTINUOUS compactly supported observables. The
note quantifies over φ ∈ C_c^∞; this part upgrades the observable
class so the Lean premise matches the note verbatim.

**Seabed:** laplace, branch `tide/germbij-singular-point` (stacked;
parent PR #121 in flight, retargeted to main after #120 merged).

**Started:** 2026-08-10T11:30Z

## Candidate

`Laplace/Multi/SingularSmooth.lean`:

1. `exists_smooth_bump_one_on_ball_support_in`: for 0 < R' < ρ,
   a C^∞ ψ with 0 ≤ ψ, ψ = 1 on ‖w‖ ≤ rIn (rIn := something ≤ R'),
   HasCompactSupport, and tsupport ψ ⊆ Metric.ball 0 ρ. Route:
   Mathlib `ContDiffBump` (c := 0, rIn, rOut with rIn < rOut < ρ);
   fields give smoothness, one_of_mem_closedBall, support_eq,
   nonneg.
2. Smooth gluing: if g is C^∞ on an open U and ψ is C^∞ with
   tsupport(ψ) ⊆ U, then g·ψ (extended by the zero off tsupport) is
   C^∞ globally. Pointwise: at u ∈ U, ContDiffAt.mul on the open
   set; at u ∉ tsupport ψ, eventually-zero + ContDiffAt.congr.
   (Check Mathlib first: `ContDiffOn.mul` + extension lemmas, or
   `contDiff_of_tsupport`-style helpers may already exist.)
3. `pencil_families_force_germ_eq_at_smooth`: as
   `pencil_families_force_germ_eq_at` but hfam quantified over
   ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ. Proof: extract the
   analyticity radius ρ at p for L₂ - L₁ (AnalyticAt → analyticOnNhd
   on a ball → ContDiffOn ω → C^∞ on the ball), shrink the part-1
   quadratic-bound radius R to rIn := min R (ρ/4) (the bound holds a
   fortiori), take the ContDiffBump with rOut := 2·rIn < ρ, glue,
   and rerun the part-2 composition (the endpoint needs only
   continuity of ψ, which smoothness supplies).
4. `pencil_families_force_eq_near_smooth`: locus form, same biUnion
   assembly.

## GPT-5.6 Sol

The adversarial critique (archived on the parent branch) remains the
deliberation; its step 9 (observable membership) is exactly what this
tide repairs. Consults will fire on tactical walls per the
lean-formalisation triggers.

## Vote

- Claude: the smooth-class upgrade as candidate.
- GPT-5.6 Sol (via the critique's B4 step 9): the same repair.

## Numerical check

Not feasible: structural (observable-class bookkeeping); the
quantitative content is unchanged from the audited endpoint.

## Result

`Laplace/Multi/SingularSmooth.lean` (~200 lines), all gates green
(import in Laplace.lean, fresh .olean, zero errors/warnings,
scripts/sorries clean). Compiled essentially on the first pass; the
only fix was removing an unused `IsOpen U` hypothesis from the gluing
helper (pointwise `ContDiffAt` on `U` makes openness unnecessary).

- `contDiff_mul_of_tsupport_subset`: the gluing lemma. Pointwise via
  contDiff_iff_contDiffAt; inside U the product rule on ContDiffAt,
  outside tsupport ψ the function is locally zero
  (image_eq_zero_of_notMem_tsupport + ContDiffAt.congr_of_eventuallyEq
  against the constant 0).
- `pencil_families_force_germ_eq_at_smooth`: hfam now over
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ — the note's C_c^∞ class
  verbatim. New ingredients relative to part 2: the analyticity
  radius ρ at p from HasFPowerSeriesOnBall.analyticOnNhd (per-point
  AnalyticAt on the eball, then .contDiffAt); the shrunk radius
  rIn := min R (ρ/4) with rOut := 2·rIn < ρ; the Mathlib ContDiffBump
  (the HasContDiffBump instance for finite-dimensional real normed
  spaces covers ι → ℝ); f.one_of_mem_closedBall / f.support_eq /
  f.hasCompactSupport / f.nonneg' supply the endpoint's bump
  interface; tsupport(f(· - p)) ⊆ closedBall p (2·rIn) ⊆ ball p ρ by
  closure_minimal + closedBall_subset_ball.
- `pencil_families_force_eq_near_smooth`: the locus form, same
  biUnion assembly, premise now matching thm:singular verbatim.

With this the twelve-step composition is closed end to end AT THE
NOTE'S OBSERVABLE CLASS: thm:singular (statement-level hypotheses:
continuity, nonnegativity, pointwise analyticity and common vanishing
on W₀, decay for every φ ∈ C_c^∞) is machine-checked, sorry-free.

### Suggested follow-ups

- germbij.tex: rewrite the thm:singular coverage footnote (full
  machine-checking can now be claimed; note the hypothesis phrasing:
  pointwise analyticity on W₀ rather than "analytic on a neighborhood
  of compact W₀" — pointwise is weaker, so the Lean version subsumes
  the note's setting; compactness is not needed), add markers for
  pencil_families_force_germ_eq_at(_smooth) and
  pencil_families_force_eq_near(_smooth), bump the pin — after PRs
  #120/#121 and this tide's PR merge.
- Optional cleanup for a later tide: derive the continuous-class
  theorems from the smooth-class ones (smooth ⊂ continuous premise
  direction means the smooth theorem is strictly stronger; the
  SingularPoint versions could become corollaries).
