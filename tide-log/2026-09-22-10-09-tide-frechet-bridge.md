# Tide: frechet-bridge

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: close the reviewer-summary caveat "`partialD`, not `iteratedFDeriv`" from tide `tensor-identification`.)
**Seabed:** laplace, main 344cff4
**Started:** 2026-09-22T10:11Z

## Candidates v1 (Claude)

See `gpt_frechet_bridge_prompt_v1.md` (A–D verbatim).

- A: `partialD i f w = fderiv ℝ f w eᵢ` (differentiable `f`).
- B: one rung, `partialD i (fun y => Dⁿf(y)[m]) x = Dⁿ⁺¹f(x)[Fin.cons eᵢ m]` for `ContDiff ℝ (n+1) f`.
- C: the tower `partialD … f x = iteratedFDeriv ℝ k f x ![eᵢ, …]`, `k = 1, …, 4`.
- D: `ContDiff ℝ n (L∘A)`, `fderiv ℝ (L∘A) c = 0`, `D²(L∘A)(c) = Q diag λ Qᵀ`, `D³ = rotT`, `D⁴ = rotQ` in `iteratedFDeriv`.

Prototype: all of A–D typecheck in a scratch file against main 344cff4 before the consult returned (the seabed's
`RotatedDerivatives` supplies the coordinate-line values; the bridge is 10 lines per rung).

## Numerical check

Not feasible in a new way: the statements are identities between two definitions of the same derivatives. The numerical
content (the tensors against central differences of `L∘A`) was checked in tide `tensor-identification`
(`numcheck_tensor_identification.py`: `max |FD − rotT| = 2.7e-14`, `max |FD − rotQ| = 7.6e-12`).

## GPT-6 Astra v1

Verbatim in `gpt_frechet_bridge_v1.md`. Summary: B correctly stated, outermost derivative first (`Dⁿ⁺¹f(x)[eᵢ, m] =
D(Dⁿf)(x)[eᵢ][m]`), no symmetry needed; the load-bearing hypothesis is `DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x`; cast the
whole successor `(↑(n+1) : WithTop ℕ∞)` and discharge `↑n < ↑(n+1)` by `exact_mod_cast Nat.lt_succ_self n`. Keep the
differentiability hypothesis in A (`deriv`/`fderiv` are totalised). State B with `Fin.cons`, instantiate in C by definitional
equality with `![…]`; C must rewrite *functions* (`funext`) before applying B; give each rung its minimal order. For D prefer a
compositional smoothness API (affine frame, separable potential, composition) with `fun_prop` inside; `fderiv f c = 0` via
`ContinuousLinearMap.ext` and `v = ∑ₖ vₖ eₖ`; the tensor conclusions are rewrites of the existing centre identities.
`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` is a one-dimensional-domain bridge and does not help; the left recursion is
the natural fit for outermost-first `partialD`. Vote A+B+C+D; defer arbitrary-order coordinate-word machinery.

## Vote
- Claude: A+B+C+D
- GPT-6 Astra: A+B+C+D ("Export A and B as general bridge lemmas, give C minimal-order hypotheses, and make D consist of
  smoothness plus reuse of the existing centre identities")

The prototype already follows every recommendation (minimal orders per rung, `Fin.cons` in B, `funext` rewrites in C,
`contDiff_affineFrame` + `contDiff_anharmonicPotential` + `ContDiff.sum` composition for D).

## Result

Commit `0a79778` on `tide/frechet-bridge`; `lake build` clean, `scripts/sorries` 0/0/0/0. A, B, C and D landed.
`Laplace/Multi/RotatedFrechet.lean` (     152 lines): `partialD_eq_fderiv`, `partialD_iteratedFDeriv`, `partialD1_eq_iteratedFDeriv`,
`partialD2_eq_iteratedFDeriv`, `partialD3_eq_iteratedFDeriv`, `partialD4_eq_iteratedFDeriv`, `contDiff_anharmonicPotential`,
`contDiff_affineFrame`, `contDiff_rotatedAnharmonic`, `fderiv_rotatedAnharmonic_center`, `iteratedFDeriv2_rotatedAnharmonic_center`,
`iteratedFDeriv3_rotatedAnharmonic_center`, `iteratedFDeriv4_rotatedAnharmonic_center`.

Surprises: none. The whole bridge is one ten-line rung lemma plus bookkeeping; the only friction was API spelling
(`contDiff_apply ℝ ℝ i` with both type arguments explicit, `ContDiff.sum`, no `fun_prop` theorems for `Matrix.mulVec`, and
`unfold` of a `∑` exposing `Multiset.map`). The prototype typechecked before the consult returned.
