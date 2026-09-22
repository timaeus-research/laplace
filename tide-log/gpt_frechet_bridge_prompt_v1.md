# Tide `frechet-bridge` (laplace seabed): candidates for GPT-6 Astra

## Context

Tide `tensor-identification` (`Laplace/Multi/RotatedDerivatives.lean`) identified the note's tensors for E2's rotated oscillator
`f := rotatedAnharmonic Q c lam alpha gamma : (Fin d → ℝ) → ℝ` (`f w = ∑ᵢ ℓᵢ((Qᵀ(w − c))ᵢ)`, `ℓᵢ(x) = λᵢx²/2 + αᵢx³/6 + γᵢx⁴/24`)
through *iterated one-dimensional derivatives along coordinate lines*:
`partialD i f w := deriv (fun s => f (w + s • Pi.single i 1)) 0`, with
`partialD_rotatedAnharmonic_center : partialD k f c = 0`, `partialD2_…_center : partialD j (partialD k f) c = (Q diag λ Qᵀ) j k`,
`partialD3_…_center : partialD i (partialD j (partialD k f)) c = rotT Q alpha i j k`, `partialD4_…_center : … = rotQ Q gamma i j k l`.
The reviewer summary carries the caveat "not `iteratedFDeriv`; the bridge to Fréchet derivatives is deferred until a theorem needs
it". Rather than wait, close it.

Mathlib (pinned, Lean v4.33): `iteratedFDeriv_succ_apply_left (m : Fin (n+1) → E) : iteratedFDeriv 𝕜 (n+1) f x m =
fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x (m 0) (tail m)`; `iteratedFDeriv_zero_apply (m) : iteratedFDeriv 𝕜 0 f x m = f x`;
`iteratedFDeriv_one_apply (m) : iteratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0)`;
`fderiv_continuousMultilinear_apply_const_apply (hc : DifferentiableAt 𝕜 c x) (u) (m) : fderiv 𝕜 (fun y => c y u) x m = fderiv 𝕜 c x m u`;
`ContDiff.differentiable_iteratedFDeriv (hm : m < n) (hf : ContDiff 𝕜 n f) : Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)`;
`HasFDerivAt.comp_hasDerivAt (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x`;
`HasDerivAt.smul_const`, `HasDerivAt.const_add`, `hasDerivAt_id'`; `![a, b] = Fin.cons a ![b]` definitionally (`Matrix.vecCons`).

## Candidates

**A. The directional derivative is the Fréchet derivative on a basis vector.**
`partialD_eq_fderiv (hf : DifferentiableAt ℝ f w) : partialD i f w = fderiv ℝ f w (Pi.single i 1)`, from
`HasFDerivAt.comp_hasDerivAt` on the line `s ↦ w + s • eᵢ` (derivative `eᵢ` at `0`, `w + 0 • eᵢ = w`), then `HasDerivAt.deriv`.

**B. One rung of the ladder.** For `ContDiff ℝ (n+1) f`, `m : Fin n → (Fin d → ℝ)`:
`partialD_iteratedFDeriv : partialD i (fun y => iteratedFDeriv ℝ n f y m) x = iteratedFDeriv ℝ (n+1) f x (Fin.cons (Pi.single i 1) m)`.
Proof: A (differentiability of `y ↦ iteratedFDeriv n f y m` from `differentiable_iteratedFDeriv` and
`DifferentiableAt.continuousMultilinear_apply_const`), then `fderiv_continuousMultilinear_apply_const_apply`, then
`← iteratedFDeriv_succ_apply_left` with `Fin.cons_zero`, `Fin.tail_cons`.

**C. The tower.** For `ContDiff ℝ 4 f` (hence all lower orders):
`partialD k f x = iteratedFDeriv ℝ 1 f x ![eₖ]`, `partialD j (partialD k f) x = iteratedFDeriv ℝ 2 f x ![eⱼ, eₖ]`,
`partialD i (partialD j (partialD k f)) x = iteratedFDeriv ℝ 3 f x ![eᵢ, eⱼ, eₖ]`, and the fourth, each by rewriting the inner
function with the previous level (`funext`) and applying B.

**D. E2's oscillator in Mathlib's derivative.** `ContDiff ℝ n (rotatedAnharmonic Q c lam alpha gamma)` for every `n`
(`fun_prop` after unfolding to a finite sum of polynomials in the affine coordinates), then
`fderiv ℝ f c = 0` (`c` is a critical point; `ContinuousLinearMap.ext` through `v = ∑ₖ vₖ eₖ`),
`iteratedFDeriv ℝ 2 f c ![eⱼ, eₖ] = (Q diag λ Qᵀ) j k`, `iteratedFDeriv ℝ 3 f c ![eᵢ, eⱼ, eₖ] = rotT Q alpha i j k`,
`iteratedFDeriv ℝ 4 f c ![eᵢ, eⱼ, eₖ, eₗ] = rotQ Q gamma i j k l`: the note's `H = D²L(w*)`, `T = D³L(w*)`, `Q = D⁴L(w*)` in the
canonical sense, closing the §60 caveat.

## Questions

1. Is B correctly stated (index order: `Fin.cons eᵢ m` puts the *outermost* derivative first, matching
   `iteratedFDeriv_succ_apply_left`)? Any hypothesis missing (e.g. `n + 1 ≤ N` casts in `differentiable_iteratedFDeriv`, whose `m < n`
   is in `WithTop ℕ∞`)?
2. Pitfalls with `fderiv_continuousMultilinear_apply_const_apply` (the `c` there is `iteratedFDeriv ℝ n f : E → ContinuousMultilinearMap …`;
   does the elaborator see `fun y => iteratedFDeriv ℝ n f y m` as `fun y => (c y) u`?), and with `![…]` versus `Fin.cons` in `rw`?
3. For D: the cleanest way to get `ContDiff ℝ n (rotatedAnharmonic …)` — `fun_prop` on the unfolded sum, or `ContDiff.comp` of
   `separableAnharmonic` (a finite sum of `ContDiff` polynomials of coordinates) with the affine `affineFrame`? Is
   `contDiff_finset_sum`/`ContDiff.sum` the right lemma name in current Mathlib?
4. Is there a shorter route via `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` or `iteratedFDeriv_succ_apply_right` that avoids
   B's induction? Scope and vote (A+B+C+D)?
