# Tide: germbij-littleo

**Direction (user):** continue the germbij arc (auto mode): the IsLittleO
packaging of the contradiction, from the recorded follow-up list. A
kappa t^gamma lower bound (gamma = 1 - m - d/2 in the chain) is
incompatible with decay o(t^-N) for all N; corollary against the analytic
multivariate chain, giving Theorem 7.3's conclusion as a single Lean
statement (modulo choice of point and bump).

**Seabed:** laplace, main at 7f61c5d (arc complete through the analytic
bridge; arc-synthesis docs PR #33 in flight, no file overlap).
**Started:** 2026-08-09T07:30Z
**Worktree/branch:** laplace-tide-germbij-littleo / tide/germbij-littleo

## Candidates v1 (Claude)

**Candidate A (core lemma, general exponent).**
```
theorem lower_bound_not_superpolynomial {Δ : ℝ → ℝ} {κ T₀ γ : ℝ}
    (hκ : 0 < κ) (hbound : ∀ t, T₀ ≤ t → κ * t ^ γ ≤ Δ t)
    (hdecay : ∀ N : ℕ, Δ =o[Filter.atTop] fun t ↦ t ^ (-(N : ℝ))) :
    False
```
(rpow throughout; γ arbitrary real since generality is free). Proof: pick
N with (N:ℝ) > -γ; isLittleO_iff at ε := κ/2; for t ≥ max T₀ 1 with t > 0:
t^γ = t^(-N) * t^(γ+N) ≥ t^(-N) since γ+N > 0 and t ≥ 1; chain
κ t^(-N) ≤ κ t^γ ≤ Δ t ≤ |Δ t| ≤ (κ/2) t^(-N); divide by t^(-N) > 0 to
get κ ≤ κ/2, contradicting 0 < κ.

**Candidate B (corollary).** The analytic multivariate hypotheses of
`analytic_pencil_difference_lower_bound_multi` plus
`(fun t ↦ ∫ w, ((L₂ w - L₁ w) * ψ w) * (exp(-(t * L₁ w)) - exp(-(t * L₂ w))))
=o[atTop] fun t ↦ t ^ (-(N:ℝ))` for all N imply False. This is the
note's Theorem 7.3 contradiction verbatim (for the pencil-difference
observable g·ψ). Note the chain's lower bound is
κ * (t * t ^ (-(m:ℝ) - d/2)) = κ * t^(1 - m - d/2) for t > 0, so A
applies with γ = 1 - m - d/2 after a t^1 * t^γ' = t^(1+γ') rewrite
(Real.rpow_one, Real.rpow_add).

Claude's initial lean: A + B in one file.

## GPT-5.6 Sol v1

Saved verbatim in `tide-log/gpt56_germbij_littleo_v1.md`. Summary: A is
correct as stated; ∀ N : ℕ is the standard formulation of superpolynomial
decay (equivalent to real exponents by monotonicity); edge cases T₀ ≤ 0
and γ ≥ 0 are harmless; confirmed isLittleO_iff, Real.one_le_rpow,
Real.rpow_add, and the positive-factor cancellation; no existing Mathlib
lemma packages the contradiction directly.

## Vote

- Claude: A + B in one file.
- GPT-5.6 Sol: A + B in one file (A as a small general order lemma, B as
  the contradiction corollary of the analytic lower bound).

## Numerical check

Not feasible (a contradiction statement between asymptotic classes);
sanity instance: kappa t^{-2} vs o(t^{-3}) fails at t large since
kappa t^{-2} / t^{-3} = kappa t -> infinity.

## Result

- Branch tide/germbij-littleo, file Laplace/Decay.lean:
  lower_bound_not_superpolynomial,
  analytic_pencil_difference_not_superpolynomial.
- Two compile fixes: `mul_le_mul_right` iff-form resolved to the wrong
  namespace target (use `le_of_mul_le_mul_right`), and T₀ needed passing
  explicitly since it occurs only inside the refine hole.
- Surprise: none; the corollary states the note's Theorem 7.3
  contradiction as a single Lean negation.
