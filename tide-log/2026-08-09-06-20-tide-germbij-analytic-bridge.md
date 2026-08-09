# Tide: germbij-analytic-bridge

**Direction (user):** continue the germbij arc (auto mode): the analytic
bridge for the multivariate chain, deriving the leading-part hypotheses
(remainder bound |g - P| <= C||x||^(m+1)) from a power series with
vanishing lower diagonal terms, mirroring how the 1D chain derives its
growth bound from AnalyticAt.

**Seabed:** laplace, main at 1c40e22 (both chains complete; multivariate
turnkey in flight as PR #31).
**Started:** 2026-08-09T06:20Z
**Worktree/branch:** laplace-tide-germbij-analytic-bridge /
tide/germbij-analytic-bridge

## Candidates v1 (Claude)

**Candidate A (tail bound, minimal).** Let `g : (ι → ℝ) → ℝ` with
`HasFPowerSeriesOnBall g p 0 r` (r finite positive, or r ≤ p.radius), let
`m : ℕ`, suppose the diagonal evaluations vanish below m:
`∀ k < m, ∀ x, p k (fun _ ↦ x) = 0`, and set
`P x := p m (fun _ ↦ x)`. Claim: there exist `C ≥ 0` and `u₁ > 0` with
`∀ x, ‖x‖ ≤ 2 * u₁ → |g x - P x| ≤ C * ‖x‖ ^ (m + 1)`.
Rationale: this is exactly the `hrem` hypothesis of
`leading_part_scaled_set` / the turnkey theorem, and the standard
geometric-tail argument (norm_mul_pow_le at radius r/2, sum the tail
`Σ_{k>m} C₀ (‖x‖/ρ)^k ≤ C₀ (‖x‖/ρ)^(m+1) / (1 - ‖x‖/ρ)`) should be
Mathlib-supported. P is automatically continuous
(`ContinuousMultilinearMap` diagonal) and positively homogeneous of
degree m (multilinearity), which are the other two structural hypotheses.

**Candidate B (ContDiff route).** Same conclusion from
`ContDiff ℝ (m+1) g` near 0 with `iteratedFDeriv ℝ k g 0 = 0` for
`k ≤ m` except the m-th giving P. Rationale: weaker hypothesis, but
Mathlib's multivariate Taylor-with-remainder support is thin (taylor
theorem is 1D); likely needs a line-restriction argument. Larger delta.

**Candidate C (composed corollary).** Candidate A plus the homogeneity
and continuity packaging, composed with
`leading_part_pencil_difference_lower_bound'` to give an end-to-end
multivariate statement whose hypotheses are: power series for L₂ - L₁
with lower diagonal terms vanishing, some sphere point with P ≠ 0,
nonnegativity, quadratic domination, bump. Rationale: the arc's final
multivariate headline; but it should be a second declaration in the same
file as A, not a separate tide.

Claude's initial lean: A (with C as a same-file corollary if A lands
quickly).

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_analytic_bridge_v1.md`. Summary:
Candidate A correct as stated (including m = 0); geometric-tail route is
the lightest; confirmed `ContinuousMultilinearMap.map_smul_univ` for
homogeneity (holds for all c, so the 0 ≤ c hypothesis is immediate) and
diagonal composition for continuity; no turnkey Taylor-remainder lemma
exists in the analytic API, so A is the right foundational lemma.

## Vote

- Claude: A + composed corollary C in one file, A separately named.
- GPT-5.6 Sol: A + C in one file, A separately named.

Architectural divergence (noted, resolved in Step 3): GPT sketched the
manual tsum-tail route (hasSum + sum_add_tsum_nat_add + geometric tsum);
Claude found `HasFPowerSeriesOnBall.uniform_geometric_approx'`, which
packages the full tail bound (‖f(x+y) - partialSum n y‖ ≤ C(a‖y‖/r')^n);
at n = m+1 with the vanishing hypothesis the partial sum collapses to the
m-th diagonal term. Using the packaged lemma.

## Numerical check

Not feasible in an informative way: the statement is existential in
(C, u₁) and the underlying inequality is the geometric tail bound, which
is structural. Sanity instance by hand: g = x²y + x⁴, m = 3,
P = x²y: |g - P| = x⁴ ≤ ‖(x,y)‖⁴. Consistent.

## Result

- Branch tide/germbij-analytic-bridge, file Laplace/Multi/AnalyticBridge.lean:
  analytic_remainder_bound, analytic_pencil_difference_lower_bound_multi.
- Two trivial compile fixes (scoped ℝ≥0∞ notation; extracting 0 < a from
  Ioo membership for positivity). Built clean on the third attempt.
- Surprise: `HasFPowerSeriesOnBall.uniform_geometric_approx'` made the
  remainder bound an 18-line proof; the consult's manual tsum-tail route
  was never needed. The multivariate chain now has analytic hypotheses,
  matching the 1D chain end to end.
