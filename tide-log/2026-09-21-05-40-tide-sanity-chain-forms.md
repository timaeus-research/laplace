# Tide: sanity-chain-forms

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the Sanity on Sampling programme in the laplace seabed: the finite-chain prediction of the note (expected pooled sample variance of an AR(1) chain started at the mode, E1/E2/E4) and the ULA-corrected LLC in trace form with its bounds (E1).
**Seabed:** laplace, commit ee83216 (origin/main at tide start; the sampler-laws tide landed at f760ed6, the Rosenbrock tide `sanity-closed-forms` is being merged in parallel)
**Started:** 2026-09-21T04:53Z
**Worktree / branch:** learning-theory/lean/laplace-tide-sanity-chain-forms, tide/sanity-chain-forms
**Retrospective:** skipped by user instruction for this auto run.

## Seabed snapshot

- `Laplace/Sampler/Lyapunov.lean`: `covStep`, Lyapunov solvers, `orthoOf`/`spectral_real`, finite-time identity, scalar `ar1_var_iterate`.
- `Laplace/Sampler/ULA.lean`: `ulaCov P h = (P - (h/2)P²)⁻¹`, `ulaCov_conj_apply` (eigenbasis entries), `ulaCov_posDef`, minibatch entries.
- Nothing on stochastic processes; no inner-product-space formulation of chains.

## Candidates v1 (Claude) and GPT-6 Astra v1

Deliberated together with the Rosenbrock candidate in the previous tide: candidates B (AR(1) finite chain in inner-product form: second-moment table, window sums, Toeplitz identity, pooled expected sample variance over C chains) and C (`trace(P · ulaCov P h) = Σ 1/(1 - h p_i/2)`) of `tide-log/gpt_sanity_closed_forms_prompt_v1.md`; GPT-6 Astra's response `tide-log/gpt_sanity_closed_forms_v1.md` (copies in this worktree) confirmed both, asked for `N > 0`, `C > 0` and the divisor-`CN` convention in B, proposed the four-layer organisation (Gram identity, orthogonal-chain pooling, AR(1) Gram table, Toeplitz sum), and for C the follow-ons `LLC_ULA - d/2 = ½ Σ (hp_i/2)/(1 - hp_i/2)` and `d/2 ≤ LLC_ULA ≤ d/(2(1 - h p_max/2))`, noting that the note's "100 at h p_max = 1.9" holds only for an isotropic spectrum.

## Integration (Claude)

Take B in full (structure `AR1Chain` in a real inner product space with white noise `⟪η j, η k⟫ = v δ_jk`; explicit sum `x k = Σ_{j<k} ρ^j η (k - j)`; Gram table `⟪x k, x l⟫ = v/(1-ρ²)(ρ^(l-k) - ρ^(k+l))` for `k ≤ l`; window sums over `i < N` of draws `x (b+1+i)`; Toeplitz identity `Σ_{i,j<N} ρ^dist(i,j) = N + 2Σ_{m<N} (N-(m+1)) ρ^(m+1)`; pooled expected sample variance over `Fin C` chains with mutually orthogonal noise) and C with GPT's bounds. Labelled as second-moment (Gram) theorems; the L² instantiation is a follow-up.

## Vote
- Claude: B + C.
- GPT-6 Astra (previous consult): B and C correct, recommended as a separate excursion from A; organisation as above.

Agreed (carried over from the previous round).

## Numerical check

Recorded in the previous tide's log: Monte Carlo (4·10⁵ chains, ρ = 0.9, v = 1, N = 12, b = 5, C = 3) pooled expected sample variance 3.6332 ± 0.0035 vs closed form 3.6362; Gram table to MC precision; Toeplitz identity exact. C: algebraic consequence of `ulaCov_conj_apply`.

## Result

- Commit `cc4e10b` on `tide/sanity-chain-forms` (base ee83216), merged with upstream in `7c709f2`, `d9d8c69`. Full `lake build` green; `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide.
- `Laplace/Sampler/AR1.lean` (     227 lines): `AR1Chain` (structure: `x 0 = 0`, `x (k+1) = ρ • x k + η (k+1)`, white noise `inner ℝ (η j) (η k) = if j = k then v else 0`), `x_eq_sum`, `inner_η_x`, `inner_x_x` (Gram table), `norm_x_sq`, `inner_x_x_dist`, `sum_norm_sq_window`, `norm_sum_window_sq`, `sum_sum_pow_dist` (Toeplitz), `inner_x_x_of_orthogonal`, `pooled_sample_variance` (the note's finite-chain prediction).
- `Laplace/Sampler/ULA.lean` additions: `orthoOf_transpose_mul_mul`, `ulaCov_conj_eq_diagonal`, `trace_mul_ulaCov` (`trace (P Σ_ULA) = Σ 1/(1 - h p_i/2)`), `ula_llc`, `sum_one_div_one_sub_eq` (excess over d), `sum_one_div_one_sub_bounds` (`d ≤ … ≤ d/(1 - h pmax/2)`).
- Surprises: `⟪x, y⟫_ℝ` is not usable as written in the current Mathlib pin (scoped notations only); explicit `inner ℝ x y` throughout. The explicit closed form `x k = Σ_{j<k} ρ^j • η (k - j)` made every Gram computation a one-line `Finset.sum_eq_single` or geometric sum; the Toeplitz identity went through by induction with `Finset.sum_range_reflect`. No mathematical surprises; GPT-6 Astra's correction that the "100 at h p_max = 1.9" figure needs an isotropic spectrum is recorded as the bounds theorem.
