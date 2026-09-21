# Tide: Gaussian moments of order 4 and 6 for a positive definite precision

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide continues the `gaussian-moments-posdef` tide, which discharged the seabed's second-moment package `FubiniIBPHypothesis` for `matCLM P`, `P.PosDef`.)
**Seabed:** laplace, `main` at 435b651 plus `tide/gaussian-moments-posdef` (f33c278) merged in; worktree `laplace-tide-gaussian-moments-high`, branch `tide/gaussian-moments-high`
**Started:** 2026-09-21 (UTC, see file name)

## Context

The seabed's explicit second-order covariance (`Laplace/Multi/CovarianceExplicit.lean`, the primer's `lem:laplace_cov2`) and the Wick formulas `gaussian_fourth_moment_formula` / `gaussian_sixth_moment_formula` take the hypothesis packages

- `LaplaceCovHypotheses H Hinv` (symmetry, right inverse, injectivity, `Z > 0`, integrability of `gW`, `u_k u_j gW`, `u_j (Hu)_i gW`, and `FubiniIBPHypothesis`);
- `LaplaceCov4MomentHypotheses` (extends with `int_4moment`, `int_3_Hl`, `fubini_ibp_cubic`);
- `LaplaceCov6MomentHypotheses` (extends with `int_6moment`, `int_5_Hl`, `fubini_ibp_quintic`),

none of which the seabed ever discharges from a positivity assumption. The previous tide discharged every field of the first package for `H = matCLM P`, `Hinv = matCLM P⁻¹` with `P.PosDef` (module `GaussianMomentsPosDef.lean`: `whiteningOf`, `integral_comp_mulVec`, product Gaussian integrals on `ι → ℝ`, `fubiniIBPHypothesis_matCLM`). The sanity note's second-order term (E7, `Cov = S + S Π S`) is a Wick-4/Wick-6 computation, so discharging the two higher packages is what makes the seabed's explicit second-order covariance apply to a Gaussian with only `P.PosDef`.

## Candidates v1 (Claude)

**A. Discharge the 4th- and 6th-moment packages by a general-`n` Gaussian integration by parts.** For `P.PosDef`, `A : Fin n → ι`, `l : ι`, with `gW := gaussianWeight (matCLM P)`:

1. `integrable_prod_coord_mul_gaussianWeight_matCLM`: `Integrable (fun u => (∏ s, u (A s)) * gW u)`;
2. `integrable_prod_coord_mul_apply_gaussianWeight_matCLM`: `Integrable (fun u => (∏ s, u (A s)) * (matCLM P u) l * gW u)`;
3. `gaussian_ibp_prod_matCLM` (the IBP identity in the seabed's "δ minus contraction" form):
   `∫ u, ((∑ r, if l = A r then ∏ s, (if s = r then 1 else u (A s)) else 0) * gW u - (∏ s, u (A s)) * (matCLM P u) l * gW u) = 0`;
4. `gaussian_stein_matCLM` (Isserlis in Stein form, contracting 3 with `P⁻¹`):
   `∫ u, u j * (∏ s, u (A s)) * gW u = ∑ r, P⁻¹ j (A r) * ∫ u, (∏ s, if s = r then 1 else u (A s)) * gW u`;
5. `laplaceCovHypotheses_matCLM`, `laplaceCov4MomentHypotheses_matCLM`, `laplaceCov6MomentHypotheses_matCLM` by instantiating 1–3 at `![a,b,c]`, `![a,b,c,d]`, `![a,b,c,d,e]`, `![a,b,c,d,e,f]` (`Fin.prod_univ_three` … `Fin.sum_univ_five`);
6. corollaries: `gaussian_fourth_moment_matCLM` (`∫ u_a u_b u_c u_d gW = Z (P⁻¹_ad P⁻¹_bc + P⁻¹_bd P⁻¹_ac + P⁻¹_cd P⁻¹_ab)`) and `gaussian_sixth_moment_matCLM` (15 terms) from the seabed's Wick formulas via `matCLM_single`.

Route: whitening `u = M v` (`M = whiteningOf hP`, `Mᵀ P M = 1`, `M Mᵀ = P⁻¹`, so `P M Mᵀ = 1`), then everything is about the standard Gaussian density `e^{-|v|²/2}` on `ι → ℝ`:

- exponent form: `∫ (∏ i, v i ^ c i) e^{-|v|²/2} = ∏ i, m (c i)` with `m n := ∫ x^n e^{-x²/2}` (`integral_fintype_prod_volume_eq_prod`), and integrability (`Integrable.fintype_prod`);
- 1D Stein: `m (n+2) = (n+1) m n`, `m 1 = 0` (from the seabed's `integral_pow_mul_exp_neg_sq_half` = `(2k-1)‼ √(2π)` and `integral_pow_mul_exp_neg_sq_odd`);
- exponent-form Stein on `ι → ℝ`: `∫ (∏ i, v i ^ Function.update c j (c j + 1) i) e = (c j) * ∫ (∏ i, v i ^ Function.update c j (c j - 1) i) e`;
- index form via `∏ s ∈ t, v (k s) = ∏ i, v i ^ #{s ∈ t | k s = i}` (`Finset.prod_fiberwise`); the "replace the r-th factor by 1" form of `∏_{s ≠ r}` keeps every product over `Fin n` and every sum over `Fin n → ι`;
- products of linear forms `∏ s, (M v) (A s)` by `Finset.prod_univ_sum` (one multi-sum over `k : Fin n → ι`), Stein for those, then the contraction `∑_k (P M)_{l k} M_{A r, k} = δ_{l, A r}`.

Rationale: it is the direct continuation of the previous tide and unlocks the seabed's whole `CovarianceExplicit` for PD Gaussians. Closed forms: the Wick sums above (numerical check below).

**B. General Isserlis for `matCLM P`** as a sum over perfect matchings of `Fin n`. Combinatorially heavy in Lean (matchings of `Fin n`); the Stein-form recursion (A.4) carries the same information and is what the seabed's explicit formulas consume. Proposed as out of scope.

**C. Slicing route.** Prove `∫ ∂_l f · gW = ∫ f · (Pu)_l · gW` for `C¹` `f` of polynomial growth directly on `ι → ℝ` by Fubini along coordinate `l` (`MeasurableEquiv.piEquivPiSubtypeProd` or marginal integrals) and 1D integration by parts, then read off cubic and quintic from derivative computations. More general than A.3 but depends on Bochner-integral slicing API that may be thin; the polynomial-growth domination also has to be built.

Claude's preference: A (with A.4 included as it is a two-line corollary of A.3).

## GPT-6 Astra v1

Saved verbatim in `gpt_gaussian_moments_high_v1.md`. Summary: A.1–A.4 correct as written (no missing `Z` in the Stein form; the contraction `(PM)Mᵀ = 1` needs no transpose fix; the `c_j = 0` edge case of the exponent Stein is harmless but should be split explicitly); the 15-term sixth moment grouped by the partner of `f` agrees with pairing `f` first and applying the fourth-moment pattern. Votes **A**, modified: use `t.erase r` products internally and a standard-Gaussian Stein helper for products of linear forms; expected Lean bottleneck is the count identity converting exponent-form Stein back to index form. Recommends against C (coordinate slicing) for lack of a cheap Bochner slicing lemma. Not aware of a ready-made Isserlis in Mathlib at this pin.

## Candidates v2 (Claude): same target, lighter architecture

While the consult ran I found that the seabed already proves a Stein identity in the `EuclidD d` world (`GaussianStein.stein_quadKernel`) by calling Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`), which holds on any finite-dimensional space with an additive Haar measure, so on `ι → ℝ` with `volume`. Its hypotheses are three integrability facts (`f' g`, `f g'`, `f g`) and differentiability of `f` and `g`. That removes the whole exponent-form Stein / 1D recursion / count-identity layer GPT flagged as the bottleneck:

- **A.3 (IBP identity)** becomes: `f u := ∏ s, u (A s)` (differentiable, `HasFDerivAt.finset_prod`; `fderiv f u (e_l) = ∑ r, (∏ s ∈ univ.erase r, u (A s)) * (if A r = l then 1 else 0)`) and `g := gaussianWeight (matCLM P)` (`fderiv g u (e_l) = -(P u)_l * g u`, from `quadForm` bilinear and `P` symmetric). Mathlib IBP then gives `∫ f (Pu)_l gW = ∫ (∂_l f) gW`, i.e. the seabed's "δ minus contraction" identity after rewriting `∏ s ∈ univ.erase r` as the "replace the r-th factor by 1" product (`Finset.prod_erase`).
- **Integrability** (A.1, A.2, the `int_*` fields) stays on the whitening route: `∏ s, (M v) (A s) = ∑ k : Fin n → ι, (∏ s, M (A s) (k s)) * ∏ s, v (k s)` (`Finset.prod_univ_sum`, `Fintype.piFinset_univ`), and a monomial `∏ s, v (k s)` in fiberwise/exponent form `∏ i, v i ^ #{s | k s = i}` (`Finset.prod_fiberwise`) times `e^{-|v|²/2}` is a product of 1D integrable functions (`Integrable.fintype_prod`, `integrable_pow_mul_exp_neg_sq_div_two`). The extra factor `(P u)_l = ∑ k, P l k * u k` is one more coordinate: `Fin.cons`/`Fin.snoc` on `A`.
- **A.4 (Stein/Isserlis recursion for `gW_P`)** is A.3 contracted with `P⁻¹`, unchanged. A.5, A.6 unchanged.

This is the `ι → ℝ` counterpart of the seabed's `EuclidD d` Stein identity; the two worlds are bridged neither here nor there (the Covariance arc lives on `ι → ℝ`).

## Vote
- Claude: candidate A (target as in v1; architecture as in v2, IBP via Mathlib)
- GPT-6 Astra: candidate A (modified: erase products internally, linear-form Stein helper)

Agreed on the target. The architectural divergence (exponent-form Stein vs Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) is resolved in Step 3 in favour of the latter, since it is already the seabed's own idiom in `GaussianStein.lean`.

## Numerical check

`scratchpad/numcheck11.py`, `P = [[2, 0.6], [0.6, 1.5]]`, `S = P⁻¹`, `Z = 2π/√det P`, scipy `dblquad` on `[-12, 12]²` (agreement to 1e-15 relative):

| quantity | quadrature | closed form |
| --- | --- | --- |
| `E[x²y²]` | 0.5337465564738292 | `S₁₁S₂₂ + 2S₁₂²` = 0.5337465564738291 |
| `E[x⁴]` | 0.9684917355371901 | `3S₁₁²` = 0.9684917355371898 |
| `E[x³y]` | -0.387396694214876 | `3S₁₁S₁₂` = -0.387396694214876 |
| `E[x⁴y²]` | 1.0858846731780616 | `3S₁₁²S₂₂ + 12S₁₁S₁₂²` = 1.0858846731780614 |
| `E[x⁶]` | 2.7513969759579253 | `15S₁₁³` = 2.7513969759579258 |
| Stein `E[x·xy²]` | 0.5337465564738292 | `S₁₁E[y²] + 2S₁₂E[xy]` = 0.5337465564738293 |
| cubic IBP, `A = (x,x,y)`, `l = x` | `E[2xy]` = -0.45454545454545464 | `E[x²y (Pu)ₓ]` = -0.45454545454545453 |
