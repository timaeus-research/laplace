# Tide: rosenbrock-e5

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: the E5 findings of the Sanity on Sampling note for the `d = 2` Rosenbrock valley — "its Laplace covariance is wrong along the *stiff* direction by a factor `1 + 200/t`: 20% at `t = 1000`", "the whole-covariance Frobenius norm hides this because flat directions dominate it", "the exact LLC is 1 at every `t`" — as exact corollaries of the seabed's closed-form Rosenbrock covariance.
**Seabed:** laplace, commit e82e49f (branch off main)
**Started:** 2026-09-21-17-45 UTC

## Context

`Laplace/TwoD/Rosenbrock.lean` (tides `oneloop-rosenbrock`, `valley-quadratic`): `rosenbrock a p = (a (p.2 - p.1^2)^2 + (1 - p.1)^2)/2`, `rosenHess a =
!![1 + 4a, -2a; -2a, a]`, `rosenCov a t` (the exact Gibbs covariance matrix) with `rosenCov_eq_laplace_add : rosenCov a t = (t • rosenHess a)⁻¹ +
(2/t^2) • !![0, 0; 0, 1]` and `rosenHess_smul_inv : (t • rosenHess a)⁻¹ = (1/t) • !![1, 2; 2, 4 + 1/a]`; `gibbsExpectation_quadValley_self : ⟨L⟩ = 1/t`
for every quadratic valley, and `rosenbrock_eq_quadValley`.

## Candidates v1 (Claude)

With `w = (2, -1)` (the stiff direction: `rosenHess a *ᵥ w = 10a • w + (4, 0)`, an eigenvector up to `O(1/a)`) and `f = (1, 2)` (the flat direction,
tangent to the valley `y = x^2` at `(1,1)`):

**A. The stiff-direction factor.** `wᵀ (tH)⁻¹ w = 1/(a t)` and `wᵀ rosenCov w = 1/(a t) + 2/t^2 = (1 + 2a/t) · wᵀ (tH)⁻¹ w`: the exact variance along
the stiff direction exceeds the Laplace value by the factor `1 + 2a/t`, i.e. `1 + 200/t` at `a = 100` (20% at `t = 1000`, 2% at `10^4`).
**B. The flat direction is barely affected.** `fᵀ (tH)⁻¹ f = (25 + 4/a)/t` and `fᵀ rosenCov f = (25 + 4/a)/t + 8/t^2 = (1 + 8/(t(25 + 4/a))) · fᵀ (tH)⁻¹ f`
(`1 + 0.00032` at `a = 100`, `t = 1000`).
**C. The Frobenius norm hides it.** `∑_ij (rosenCov - (tH)⁻¹)_ij^2 = 4/t^4` and `∑_ij ((tH)⁻¹)_ij^2 = (9 + (4 + 1/a)^2)/t^2`, so the relative
squared Frobenius error is `4/(t^2 (9 + (4 + 1/a)^2))`: relative error `2/(t sqrt(9 + (4+1/a)^2)) ≈ 0.4/t`, against `200/t` along the stiff direction.
**D. The exact LLC is 1.** `t · ⟨rosenbrock a⟩_t = 1` for every `t > 0` (from `gibbsExpectation_quadValley_self`).

Proposed: A + B + C + D, one module `Laplace/TwoD/RosenbrockE5.lean` (~150 lines of `Fin 2` matrix arithmetic).

## Numerical check

`numcheck27.py` (`a = 100`): stiff ratio along `(2,-1)`: `1.20000` at `t = 1000`, `1.02000` at `t = 10^4` (`= 1 + 2a/t`); along the exact stiff
eigenvector (`0.046°` from `(2,-1)`): `1.19968`; flat ratio `1.000319 = 1 + 8/(t(25 + 4/a))`; relative Frobenius error `0.00040 = 2/(t |S|_F)`.

## GPT-6 Astra v1

Saved verbatim in `gpt_rosenbrock_e5_v1.md`. Summary: A–D sound; caught the factor-of-two slip in the eigenvector remark (`H w = 5a w + (2,0)`,
not `10a w + (4,0)` — the latter is the Hessian of the loss without the `1/2`), already corrected in the module; `w` is exactly the valley
*normal* and `f` exactly the tangent, neither an exact eigenvector, approaching the stiff/flat eigendirections as `a → ∞` — call `w` the
"valley-normal (stiff-proxy) direction"; along the exact unit stiff eigenvector `v₊` the factor is `1 + 2λ₊ v₊,y²/t` with
`2λ₊ v₊,y² = 2a - 8/25 + O(1/a)`, which explains `1.19968` vs `1.2` (a difference `-8/(25t)`, not `O(1/a)` at fixed `t`); state the
multiplicative identities (not literal quotients) plus the two closed forms; exact rational corollaries `6/5` (`t = 1000`) and `51/50`
(`t = 10^4`) at `a = 100`; explicit `∑ i j, (M i j)^2` is the right Frobenius form. **Vote: A+B+C+D.**

## Vote
- Claude: A+B+C+D (with the two rational corollaries)
- GPT-6 Astra: A+B+C+D

Agreed.

## Result

Committed on `tide/rosenbrock-e5` at 91d8cf8 (`lake build` clean, `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide). New module `Laplace/TwoD/RosenbrockE5.lean`: `rosenHess_mulVec_stiff`, `laplace_stiff`, `rosenCov_stiff`, `rosenCov_stiff_ratio` (factor `1 + 2a/t`), `rosenCov_stiff_ratio_100_1000` (`6/5`), `rosenCov_stiff_ratio_100_10000` (`51/50`), `laplace_flat`, `rosenCov_flat_ratio` (`1 + 8/(t(25 + 4/a))`), `rosenCov_frobenius_sq` (`4/t⁴`), `laplace_frobenius_sq` (`(9 + (4 + 1/a)²)/t²`), `rosenCov_frobenius_rel`, `rosenbrock_llc`.

Surprises: (i) the eigenvector remark in the first draft had `H w = 10a w + …`; the correct identity is `H (2,-1) = 5a (2,-1) + (2,0)` (GPT flagged the same slip independently); (ii) the rational corollaries need the scalar numerals pinned to `ℝ` (`((1000 : ℝ) • rosenHess (100 : ℝ))⁻¹`) or `rw` cannot unify the general lemma against them.
