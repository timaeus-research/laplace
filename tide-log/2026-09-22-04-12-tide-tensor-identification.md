# Tide: tensor-identification

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: close the "rotated tensors are stated, not proved" caveat of the E2/E7 matrix-form tides.)
**Seabed:** laplace, branch `tide/covK-rate` = main df3f222
**Started:** 2026-09-22T04:12Z

## Candidates v1 (Claude)

See `gpt_tensor_identification_prompt_v1.md` (A–C verbatim).

- A: the Taylor identity `rotatedAnharmonic Q c lam alpha gamma (c + v) = ½ v⬝(Hv) + (1/6)∑ rotT v³ + (1/24)∑ rotQ v⁴` (and `= 0` at `c`),
  the seabed's Rosenbrock-style certification of the tensors.
- B (stretch): coordinate partial derivatives `∂ᵢ∂ⱼ∂ₖ (L∘A)(c) = rotT i j k` etc. via `deriv` along coordinate lines.
- C: an `iteratedFDeriv` route (only if cheap).

## GPT-6 Astra v1

Saved verbatim in `gpt_tensor_identification_v1.md`. Summary: A is the right Taylor-coefficient certificate (the `1/3!`, `1/4!` over all
ordered index tuples are correct; include the symmetry of `H`, `rotT`, `rotQ`, since a diagonal contraction only determines the symmetric
part; orthogonality of `Q` and positivity are not needed); prove three contraction lemmas by `Finset.sum_mul_sum`/`Finset.mul_sum` and
controlled reordering, then assemble. B: coordinate-line `deriv` is the right interface; build a `HasDerivAt` helper for
`fun s => ∑ l, g l (a l + s * b l)` from `HasDerivAt.comp/add/mul_const/sum`, keep differentiability hypotheses (`deriv` is totalised),
differentiate an explicit polynomial tower `P₀…P₄`, and prove the partial-derivative identities *for every `w`* before nesting (never
differentiate an equality at `c`). C (`iteratedFDeriv`) deferred. Vote: A+B, A independently shippable.

## Vote
- Claude: A+B
- GPT-6 Astra: A+B

## Numerical check

`numcheck_tensor_identification.py` (`d = 3`, random `Q, c`, central differences `h = 0.01`): `F(c) = 0`, gradient `≈ 3e-5 = O(h²)`;
`max |FD − H| = 2.7e-4` (`O(h²)`), `max |FD − rotT| = 2.7e-14`, `max |FD − rotQ| = 7.6e-12`.
