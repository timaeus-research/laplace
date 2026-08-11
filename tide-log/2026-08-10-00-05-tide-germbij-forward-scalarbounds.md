# Tide: germbij forward programme stage 5b (scalar quantitative bounds)

**Direction (user):** "Yes continue with germbij, and do not switch into
another seabed... the main core concern being the recovery of all
coefficients in the nondegenerate case and the main theorem in the
nondegenerate case."

**Seabed:** laplace, branch tide/germbij-forward-coefffn at 20f99e3
(stacked; stage 5a in PR #100). Architecture consult archived as
`tide-log/gpt56_stage5_shape_v1.md` (stage-5a tide); this tide is its
item 5 (kept scalar/algebraic per the consult).

**Started:** 2026-08-10T00:05Z

## Candidates (consult section "Tide 5b")

1. `factorial_mul_factorial_le_factorial_add` (ℕ) from Mathlib's
   divisibility fact.
2. `real_exp_eq_tsum` and the **unrestricted exponential Taylor
   remainder** `|exp x - ∑_{i≤N} x^i/i!| ≤ |x|^(N+1)·exp|x|/(N+1)!`
   for ALL real x (tsum shift + termwise factorial comparison), the
   replacement for Real.exp_bound's |x| ≤ 1 restriction that fails on
   the mesoscopic window.
3. `abs_exp_sub_one_le'`: `|e^y - 1| ≤ |y|e^|y|` unrestricted, and the
   perturbation bound `|e^{-(A+δ)} - e^{-A}| ≤ |δ|·e^{|A|+|δ|}`
   (consult's exact suggested shape, coarse but Gaussian-absorbable).
4. Degree bounds `natDegree (gradedExpPoly a N) ≤ N·N` and the
   z-uniform polynomial tail bound
   `|eval q - ∑_{j≤N} c_j q^j| ≤ q^(N+1)·∑_{j∈Ico(N+1)(N²+1)} |c_j|`
   for q ∈ [0,1] (uniform indexing bound per the consult, so the
   bound does not depend syntactically on z after instantiation).

## Numerical check

Feasible for the remainder inequality; executed before writing Lean
(see Result): checked `|exp x - S_N(x)| ≤ |x|^{N+1} e^{|x|}/(N+1)!` at
x ∈ {-3, -0.5, 0.5, 5}, N ∈ {0, 2, 5}, and the tail bound at the
stage-4 test coefficients with q = 0.3.

## Result

`Laplace/Multi/ScalarBounds.lean` (~230 lines), all gates green:

- `factorial_mul_factorial_le_factorial_add`, `real_exp_eq_tsum`
  (via NormedSpace.expSeries_div_hasSum_exp; the exp_eq_tsum_div
  rewrite route dies at whnf).
- `abs_exp_sub_sum_le`: the unrestricted exponential Taylor remainder
  (tsum shift via Summable.sum_add_tsum_nat_add, termwise factorial
  comparison, norm_tsum_le_tsum_norm by defeq of ‖·‖ and |·| on ℝ).
- `abs_exp_sub_one_le'` (nlinarith from add_one_le_exp at ±y),
  `abs_exp_neg_add_sub_exp_neg_le` (the Gaussian-absorbable
  perturbation bound).
- `natDegree_exponentPoly_le` (≤ N), `natDegree_gradedExpPoly_le`
  (≤ N·N), `gradedExpPoly_tail_bound` (z-uniform indexing bound
  N²+1, per the consult).

Numerical checks passed before writing (remainder inequality at 12
(x, N) pairs; tail bound at the stage-4 coefficients).

Surprises: two whnf heartbeat timeouts (catalogued class) around
NormedSpace.exp instance unification and the tsum comparison chain —
both cleared by the documented maxHeartbeats bump. `tsum_le_tsum` is
now dot-notation `Summable.tsum_le_tsum` on the LHS summability.
`simpa [Real.norm_eq_abs]` over-normalizes (pushes abs inside
div/pow); on ℝ use norm lemmas directly by defeq instead.

### Suggested follow-ups

- Stage 5c-pre (next): the T₂/H bridge, named Gaussian rate,
  arbitrary-small Peano window control, and the Gaussian absorption
  lemma (consult items 1-3).
- Then the majorant + DCT + numerator_hasExpansion (consult items
  6-9).
