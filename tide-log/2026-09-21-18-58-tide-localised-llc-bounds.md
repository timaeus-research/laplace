# Tide: localised-llc-bounds

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: E3/E6 closures for the localised LLC.
**Seabed:** laplace, commit aa6712a (main, after `llc-variance`)
**Started:** 2026-09-21 (UTC, see filename)

## Context

E3 of the sanity note ("localisation"): "The LLC shrinks as `½ t tr(H(tH + γI)⁻¹)`: measured 4.23, 2.55, 0.83 against predicted 4.20, 2.50,
0.80 at `γ_rel = 1, 10, 100`; … A localised LLC is therefore not `d/2` even for a quadratic, and the Hessian route says by how much."
E6: "Note that a localised LLC is the Hessian quantity `½ t tr(H(tH + γI)⁻¹)`, not `d/2`: localisation makes the problem regular by hand,
at the price of changing what is measured." Here `γ_rel = γ/(t λ_min)` and `κ = λ_max/λ_min`.

Seabed: `Laplace/Multi/TiltedGaussian.lean` has the localised target as a tilted Gaussian and `localised_llc`:
`t ⟨½ wᵀHw⟩ = ½ ∑ᵢⱼ (tH)ᵢⱼ ((tH+γI)⁻¹)ᵢⱼ + ½ t mᵀHm` (with `localised_llc_unlocalised`: `d/2` at `γ = 0`). The value is in matrix-entry form
only; nothing is known about it as a function of `γ`. `Laplace/Sampler/Lyapunov.lean` has `spectral_real` (`A = U diag(λ) Uᵀ`),
`Laplace/Sampler/ULA.lean` the conjugation lemmas (`orthoOf_transpose_mul_mul`, `ulaCov_conj_eq_diagonal`, `trace_mul_ulaCov`) that turn a
matrix function of `P` into its eigenvalue sum.

## Candidates v1 (Claude)

Let `H` be positive definite with eigenvalues `λᵢ = hH.1.eigenvalues i`, `t > 0`, `γ ≥ 0`, `d = |ι|`.

**A. Eigen form of the localised LLC.**
```
localisedLLC_eq_sum_eigen :
  ½ ∑ᵢⱼ (t • H) i j * ((t • H + γ • 1)⁻¹) i j = ½ ∑ᵢ t λᵢ/(t λᵢ + γ)
```
via `(orthoOf hH.1)ᵀ (tH + γ1)⁻¹ (orthoOf hH.1) = diagonal (1/(tλᵢ + γ))` (`localised_inv_conj_eq_diagonal`) and the trace form
`∑ᵢⱼ Aᵢⱼ Bᵢⱼ = trace(Aᵀ B)`. Corollary on the Gibbs side (`localised_llc_centred`): for `w₀ = w*`,
`t · tiltedExpectation (tH + γ1) 0 (½ uᵀHu) = ½ ∑ᵢ t λᵢ/(t λᵢ + γ)`.

**B. Behaviour in `γ`** (pure algebra on the eigen form, `Λ(γ) := ½ ∑ᵢ t λᵢ/(t λᵢ + γ)`):
```
localisedLLC_zero        : Λ(0) = d/2
localisedLLC_antitone    : γ ≤ γ' → Λ(γ') ≤ Λ(γ)      (on γ ≥ 0)
localisedLLC_lt_half_dim : 0 < γ → 0 < d → Λ(γ) < d/2
localisedLLC_pos         : 0 < d → 0 < Λ(γ)
localisedLLC_tendsto_zero: Tendsto Λ atTop (nhds 0)
```

**C. The `κ`/`γ_rel` bounds.** With `λ_min ≤ λᵢ ≤ λ_max`, `κ = λ_max/λ_min`, `γ_rel = γ/(t λ_min)`:
```
localisedLLC_bounds : d/(2(1 + γ_rel)) ≤ Λ(γ) ≤ d/(2(1 + γ_rel/κ))
```
(each term `tλᵢ/(tλᵢ+γ) = 1/(1 + γ/(tλᵢ))` is increasing in `λᵢ`). At `γ_rel = 100`, `κ = 100` this gives `Λ ∈ [d/202, d/4]`; the
note's `0.80` for `d = 10` sits inside.

**D. The E3 trace-ratio remark.** "`(tH)⁻¹` overpredicts by a factor 25 at `γ_rel = 100`": `tr((tH)⁻¹)/tr((tH+γI)⁻¹)` is spectrum-specific;
the general statement is the per-direction factor `(tλᵢ+γ)/(tλᵢ) = 1 + γ_rel λ_min/λᵢ ∈ [1 + γ_rel/κ, 1 + γ_rel]`
(`localised_variance_ratio_bounds`). Cheap after A.

Vote intention: A+B+C, D if cheap.

## Numerical check

`numcheck30.py`: `d = 10`, log-uniform spectrum with `κ = 100`, `t = 100`:
```
gamma_rel=       0: Lambda=5.0000 (trace form 5.0000)  bounds [5.0000, 5.0000]  ok=True
gamma_rel=       1: Lambda=4.1998 (trace form 4.1998)  bounds [2.5000, 4.9505]  ok=True
gamma_rel=      10: Lambda=2.5000 (trace form 2.5000)  bounds [0.4545, 4.5455]  ok=True
gamma_rel=     100: Lambda=0.8002 (trace form 0.8002)  bounds [0.0495, 2.5000]  ok=True
gamma_rel=1000000.0: Lambda=0.0001 (trace form 0.0001)  bounds [0.0000, 0.0005]  ok=True
monotone decreasing: True
rotated frame: 1/2 sum_ij (tH)_ij S_ij = 2.5000  vs eigen sum 2.5000
```
The eigen form reproduces the note's predicted `4.20, 2.50, 0.80` exactly, agrees with the matrix-entry form in a random orthogonal frame,
and the bounds and monotonicity hold.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_localised_llc_v1.md` (prompt in `gpt_localised_llc_prompt_v1.md`). Summary: A–D correct with `0 < λ_min ≤ λᵢ ≤ λ_max` made explicit for C/D and a nonempty index for the strict statements; `Λ` is in fact strictly decreasing; `γ_rel/κ = γ/(tλ_max)` so the upper bound is exact; the covariance-trace ratio of E3 is a weighted average of the per-direction ratios (the factor 25 is spectrum-specific). Lean: exhibit the inverse `U diag(1/(tλ+γ)) Uᵀ` and use `Matrix.inv_eq_left_inv` (route (a)); entry-sum-to-trace by unfolding `Matrix.trace`/`mul_apply` and `Finset.sum_comm`; the limit via `tendsto_atTop_add_const_left`, `tendsto_inv_atTop_zero.comp`, constant multiple, `tendsto_finset_sum`. Scope: A+B+C, add `tr((tH+γI)⁻¹) = Σ 1/(tλᵢ+γ)` opportunistically; defer the ULA-corrected localised LLC.

## Vote
- Claude: A+B+C (+ the covariance trace and D as cheap corollaries)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.

## Result

Committed on `tide/localised-llc-bounds` at 9edda86 (`lake build` clean, `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide). New module `Laplace/Sampler/LocalisedLLC.lean` (272 lines): `sum_mul_apply_eq_trace`, `orthoOf_transpose_localised_mul`, `orthoOf_transpose_localised_inv_mul`, `localisedLLC`, `localised_llc_matrix_eq_eigen`, `localised_llc_centred`, `trace_localised_inv`, `localisedLLC_zero`, `localisedLLC_antitone`, `localisedLLC_lt_half_dim`, `localisedLLC_pos`, `localisedLLC_tendsto_zero`, `localisedLLC_bounds`, `localisedLLC_bounds_kappa`, `localised_variance_ratio_bounds`.

Surprises: (i) exhibiting the inverse `U diag(1/a) Uᵀ` and using `Matrix.inv_eq_left_inv` went through in one pass once the product was reassociated to expose `Uᵀ M U`; (ii) `add_le_add_left h a` adds on the right in this Mathlib; (iii) the whole file checked clean on the second pass — the spectral toolkit from the ULA tides transfers directly.
