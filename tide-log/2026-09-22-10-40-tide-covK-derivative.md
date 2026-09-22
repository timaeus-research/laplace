# Tide: covK-derivative

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: eq:covK as `−∂ₜ` of the first-order eq:cov/eq:mean prediction, and the exact Gibbs identity
`Cov_t[K, ψ] = −d⟨ψ⟩_t/dt`.)
**Seabed:** laplace, main 6f2b20a
**Started:** 2026-09-22T10:49Z

## Candidates v1 (Claude)

See `gpt_covK_derivative_prompt_v1.md` (A–C verbatim).

- A: `covKFormula t H T B b = −deriv (fun s => ½ tr(B(sH)⁻¹) + b⬝meanShift s H T) t` for invertible `H`, via `covKFormula t = c/t²`
  with `c = ½ tr(BH⁻¹) − ½ b⬝(H⁻¹(T:H⁻¹))` (the second and fourth terms of eq:covK cancel at `γ = 0`).
- B: exact, one dimension: `HasDerivAt (fun s => ⟨xᵏ⟩_s) (−Cov_t[ℓ, xᵏ]) t` by dominated differentiation on `s > t/2` with the bound
  `(λ/2|x|^{k+2} + |α|/6|x|^{k+3} + γ/24|x|^{k+4}) e^{−(t/2)ℓ}` (needs `ℓ ≥ 0`, tide `unique-minimum`).
- C (optional): the `γ`-version with `S = (tH + γ)⁻¹`.

## Numerical check

`numcheck_covK_derivative.py`: `covKFormula(t) = −F'(t)` to `7e-13` (`d = 4`, random `H, T, B, b`, central differences), terms 2 + 4
of eq:covK `= 9e-19`; `Cov_t[ℓ, xᵏ] = −d⟨xᵏ⟩/dt` to `≤ 4e-10` for `k = 1, 2, 3`, `t = 2, 8` (quadrature).

## GPT-6 Astra v1

Verbatim in `gpt_covK_derivative_v1.md`. Summary: the differentiation is right; for `S = (tH + γ)⁻¹` the four displayed terms are
`−F'` *with symmetry of `S`* (to swap `bᵀS` and `(Sb)ᵀ`), while at `γ = 0` terms 2 and 4 cancel in the original ordering and
`covKFormula = t⁻²[½ tr(BJ) − ½ bᵀJ(T:J)]`, `J = H⁻¹`, with *no* symmetry needed provided the Lean constant keeps the placement
`bᵀJ(…)` (it does). Qualification: with `γ ≠ 0` the note's eq:mean also has `γS(w₀ − w*)`, whose `−∂ₜ` is `γ bᵀSHS(w₀ − w*)`,
absent from eq:covK; C is right only for the cubic-only `meanShift`. Stage A+B as a "response/consistency identity for the Laplace
prediction", not as the authors' derivation, and not as licence to differentiate remainders. B: bound and ball right; quotient rule
via `HasDerivAt.div` and a scalar identity. C: use the ring-inverse Fréchet derivative and bridge to `Matrix.inv`, with invertibility
of `tH + γ` at the point; do not differentiate `SA = 1` to *establish* differentiability.

## Vote
- Claude: A+B
- GPT-6 Astra: A+B, C optional ("formula-level consistency plus exact Gibbs response, not a theorem permitting differentiation
  of the Laplace remainder")

Adopted: A+B; C left as a follow-up; wording per GPT in the staging note.
