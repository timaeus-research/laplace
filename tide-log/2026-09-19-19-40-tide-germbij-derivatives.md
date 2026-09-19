# Tide: germbij derivative agreement

**Direction (user):** "Continue" (2026-09-19) — the tide loop continues; this tide takes the derivative upgrade that the local-uniform consult stated and sketched.
**Seabed:** laplace, commit a9bb83e (main; LocalUniform merged)
**Started:** 2026-09-19T19:40Z
**Ledger direction:** germbij: uniform beyond-all-orders agreement of the gradients D(e^{-tL2}) - D(e^{-tL1}) on compacts, from the uniform agreement of the weights and the second-derivative bound |D^2 h_t| <= B t^2 via Taylor along segments with step t^-(N+3).

## Seabed snapshot
- `eventually_uniform_abs_exp_sub_le` (LocalUniform): ∀ N ∃ C, eventually ∀ x ∈ K, |h_t x| ≤ C t^{-N}.
- `hasFDerivAt_expWeight`, `norm_expWeight_deriv_le`, `norm_fderiv_weightDiff_le`, `exists_gradient_bound_on` (LocalUniform).
- Missing: any second-derivative control of the weights; any statement about `D h_t`.

## Candidates v1 (Claude)
Notation: `h_t = e^{-tL₂} − e^{-tL₁}`, `w_i = e^{-tL_i}`, `K'' = cthickening 1 K`.

### D2. Second-derivative bound
`D w = w • (−t DL)`, so `D²w = (Dw) ⊗ (−t DL) + w • (−t D²L)` and `‖D²w(y)‖ ≤ t²‖DL(y)‖² + t‖D²L(y)‖`;
on a compact, `‖D²h_t‖ ≤ B t²` for `t ≥ 1` with `B = sup(‖DL₁‖² + ‖DL₂‖² + ‖D²L₁‖ + ‖D²L₂‖)`.

### T. Taylor along a segment
For `x ∈ K`, unit `v`, `0 < s ≤ 1` (so the segment stays in `K''`):
`|h_t(x + s v) − h_t(x) − s·Dh_t(x)v| ≤ B t² s²` (mean value applied to `σ ↦ Dh_t(x+σv)v`, whose Lipschitz
constant on `[0,s]` is `≤ Bt²`), hence `|Dh_t(x) v| ≤ (|h_t(x+sv)| + |h_t(x)|)/s + B t² s ≤ 2A_t/s + Bt² s`,
`A_t := sup_{K''} |h_t|`. Then `‖Dh_t(x)‖ ≤ 2A_t/s + Bt² s` by `opNorm_le_of_unit_norm`.

### DU. Uniform derivative agreement
```
theorem eventually_uniform_norm_fderiv_exp_sub_le (h1 h2 : ContDiff ℝ ∞) (hL1 hL2) (hexact) (hK : IsCompact K) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ᶠ t in atTop, ∀ x ∈ K, ‖fderiv ℝ h_t x‖ ≤ C * t ^ (-(N : ℝ))
```
Choose `s = t^{-(N+3)}`: `2A_t/s = 2 A_t t^{N+3} ≤ 2C t^{-N}` (uniform weight bound at exponent `2N+3` on `K''`),
`Bt² s = B t^{-(N+1)} ≤ B t^{-N}`. Pointwise corollary: `SuperPoly (fun t ↦ fderiv h_t x v)` for every `x, v`.

**Proposed tide:** D2 + T + DU (+ pointwise) in `Laplace/Multi/DerivativeAgreement.lean` (~400 lines).

## GPT-6 Astra v1 (summary; verbatim in `gpt_germbij_deriv_v1.md`)
- Second-derivative formula and bound correct: `D²w[u][v] = Dw[u](−t DL[v]) + w(−t D²L[u][v])`, `‖D²w‖ ≤ t²‖DL‖² + t‖D²L‖`.
- ENDPOINT CORRECTION: use CLOSED balls (`x + s v ∉ ball x s` for unit `v`; `closedBall x 1 ⊆ cthickening 1 K`).
- Operator norm + `opNorm_le_of_unit_norm` is right; supply nonnegativity of the bound. Nested `fderiv ℝ (fderiv ℝ w)`
  fine; expose `fderiv w = fun y ↦ w y • (−t • DL y)` as a FUNCTION equality before differentiating it.
- Taylor step: the affine-error mean value inequality `norm_image_sub_le_of_norm_fderiv_le'` on `closedBall x s` with
  `φ = Dh x`, `C = Ms` gives `|h(x+sv) − h x − Dh x (sv)| ≤ M s²` directly. Package the interpolation lemma
  independently of exponentials: `|h| ≤ A`, `‖D²h‖ ≤ M` on `closedBall x 1` ⇒ `‖Dh x‖ ≤ 2A/s + Ms`.
- Stop the public result at k = 1; higher orders need polynomial growth of all derivatives + enlarged compacts.

## Vote
- Claude: D2 + interpolation + DU + pointwise, one file `Laplace/Multi/DerivativeAgreement.lean`
- GPT-6 Astra: yes — one tide for D2 + closed-ball Taylor interpolation + DU + pointwise; defer higher orders

## Numerical check
Not feasible: inequalities and SuperPoly assertions.

## Step 3 plan
`norm_expWeight_smul_le` (any normed space), `fderiv_expWeight_eq`, `hasFDerivAt_fderiv_expWeight`,
`norm_fderiv_fderiv_expWeight_le`, `fderiv_weightDiff_eq`, `hasFDerivAt_fderiv_weightDiff`, `exists_hessian_bound_on`,
`norm_fderiv_le_of_bounds` (interpolation), `eventually_uniform_norm_fderiv_exp_sub_le`, `superPoly_fderiv_exp_sub_at`.
