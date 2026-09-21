# Tide: `eq:covK` in closed form and the variance of the loss

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide extracts the closed form of the seabed's second-order covariance coefficient for the two observables the note uses, `K = L` and the quadratic `½wᵀPw`, and derives `t² Var(L) → d/2`.)
**Seabed:** laplace, `tide/hessian-route` at aec042c (chained; `main` at c430f7a); worktree `laplace-tide-covk-closed-form`, branch `tide/covk-closed-form`
**Started:** 2026-09-21 (UTC, see file name)

## Context

`cov2Coefficient V φ ψ H Hinv a b hV hφ hψ` (now public) is
`½ trASig (A ∘ Hinv ∘ B ∘ Hinv) 1 + ½ ⟨Hinv b, Φ:Hinv⟩ − ½ ⟨b, Hinv (A (Hinv (T:Hinv)))⟩ − ½ ⟨Hinv b, T:(Hinv ∘ A ∘ Hinv)⟩`
with `A = ∇²φ`, `Φ = ∇³φ`, `B = ∇²ψ`, `T = ∇³V`; the note's `eq:covK` is the same four terms in index notation with `S = (tH)⁻¹`
(and `Φ = T` because the note's `K` is the loss itself). The previous tide packaged both `K = V` (`potentialObservable`: `A = P`, `Φ = T`)
and `K = ½wᵀPw` (`quadObservable`: `A = P`, `Φ = 0`) and proved the rate theorem `gibbsCov_first_order_rate_explicit_posDef` with only
`P.PosDef`.

## Candidates v1 (Claude)

**A. Closed forms.** With `Σ = P⁻¹` (`Hinv = matCLM P⁻¹`, `A = matCLM P`, so `A ∘ Hinv = Hinv ∘ A = id`):

1. `cov2Coefficient_quadObservable`: for `φ = ½wᵀPw`, `cov2Coefficient = ½ trASig B Σ − ⟨Σb, T:Σ⟩` (the `Φ` term is `0`, the two `T` terms coincide).
2. `cov2Coefficient_potentialObservable`: for `φ = V`, `cov2Coefficient = ½ trASig B Σ − ½ ⟨Σb, T:Σ⟩` (the `Φ = T` term cancels one of the two).
3. `potentialObservableQuintic : ObservableQuinticApprox V 0` from `PotentialQuinticApprox` (odd-part bound is the potential's own), so the rate
   theorem applies to `φ = V`: `covV_first_order_rate_posDef : |t² Cov_t(V, ψ) − (½ trASig B Σ − ½ ⟨Σb, T:Σ⟩)| ≤ C/t` — the note's `eq:covK`
   for `K = L` in closed form, with only `P.PosDef`; likewise `covK_closed_form_rate_posDef` for the quadratic observable.
4. `varV_first_order_rate_posDef : |t² Var_t(V) − d/2| ≤ C/t` (ψ = V: `b = 0`, `B = P`, `trASig P Σ = d`): the variance of the loss under the
   Gibbs posterior of a regular model is `d/(2t²)` to leading order — the regular-model value of Watanabe's singular fluctuation; and
   `varK_first_order_rate_posDef` for the quadratic observable (same limit).

Rationale: this is what the note's `eq:covK` tag should point at (its current target hides the formula inside a coefficient definition), and
`t² Var(L) → d/2` is a statement the note can quote directly. All algebra on continuous linear maps; the analysis is the previous tides'.

**B. The bridge to the note's index notation** (`Σ_{mn} T_{lmn} S_{mn}` versus `tensorContractMatrix hV.T Hinv`, and the `t`-scaling `S = (tH)⁻¹`):
needs coordinates of a `ContinuousMultilinearMap` and a second tensor representation; the seabed has private helpers (`Tcoord`). Useful but a
separate bookkeeping tide; skip here.

**C. Only 1–2** — too thin.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck18.py`: `V = ½wᵀPw + 0.3x³ + 0.2xy² + ½(x⁴ + y⁴)`, `P = [[2, 0.5], [0.5, 1]]`, `d = 2`, quadrature:
`t² Var_t(V) = 0.9279, 0.9764, 0.9935` at `t = 40, 160, 640` (→ `d/2 = 1`); `t² Cov_t(V, x₁) = −0.3322, −0.4148, −0.4454` (→ predicted
`−½ ⟨Σe₁, T:Σ⟩ = −0.4571`), both converging at the expected `O(1/t)`-type rate.

## GPT-6 Astra v1

Saved verbatim in `gpt_covk_closed_form_v1.md`. Summary: both closed forms confirmed (`ΣAΣ = Σ`, symmetry moves `Σ` across the dot
product; the four terms reduce to `½ tr(BΣ) + {0 or ½q} − ½q − ½q` with `q = ⟨Σb, T:Σ⟩`); `t² Var_t(V) → d/2` confirmed and consistent with
the numerics. Qualification on Watanabe: this coefficient *agrees numerically* with the singular fluctuation `ν = d/2` of a regular,
well-specified model, but Watanabe's functional variance is a sum of posterior variances of individual log-likelihoods, not the posterior
variance of their sum, so the theorem should not be presented as identifying the two notions (and misspecified regular models need not have
`ν = d/2`). The cubic term for the quadratic observable is twice that for the loss (suggested footnote wording recorded in the response).
Lean advice: keep unfolding local (`.A`, `.Φ` by `rfl`), reassociate `A.comp (Σ.comp X)` with `← ContinuousLinearMap.comp_assoc` and
cancel, package `trASig (B.comp Σ) 1 = trASig B Σ` and the zero contraction as helpers, reuse symmetry via `Matrix.posDef_inv_iff`. Votes **A**
with the Watanabe qualification; suggests `Tendsto` corollaries if cheap.

## Vote
- Claude: candidate A (statements phrased as rates, Watanabe qualified in the docstring)
- GPT-6 Astra: candidate A (same)

Agreed.

## Result

Committed as `Laplace/Multi/CovKClosedForm.lean` (0039aaa), 168 lines, 0 sorries, `lean-state check` clean.

Theorems: `matCLM_inv_comp`, `matCLM_inv_apply_matCLM`, `dot_matCLM_inv_symm`, `trASig_comp_one`, `tensorContractMatrix_zero`,
`comp_inv_comp_eq`, `inv_comp_comp_inv_eq`; `cov2Coefficient_quadObservable` (`½ trASig B Σ − ⟨Σb, T:Σ⟩`),
`cov2Coefficient_potentialObservable` (`½ trASig B Σ − ½ ⟨Σb, T:Σ⟩`); `potentialObservableQuintic`; `covV_first_order_rate_posDef`,
`covK_closed_form_rate_posDef`, `varV_first_order_rate_posDef` (`t² Var_t(V) → d/2`), `varK_first_order_rate_posDef`.

Surprises: none; once the coefficient was public the whole tide was two composition identities and `ring`. The Watanabe qualification
from the consult is recorded in the docstring wording ("the regular-model value of the singular fluctuation", not an identification).
