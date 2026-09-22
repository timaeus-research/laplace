# Tide: moments-sharp

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the general-`k` moment expansions that the parity-sharp `J_n` layer of `order3-parity` makes available.)
**Seabed:** laplace, branch `tide/e2-matrix` (main 7cf9194 + the e2-matrix commit)
**Started:** 2026-09-22T03:31Z

## Candidates v1 (Claude)

See `gpt_moments_sharp_prompt_v1.md` (A–C verbatim).

- A: all odd moments, `|t^{k+1}⟨x^{2k+1}⟩ + α(2k+3)‼/(6λ^{k+2})| ≤ K/t` and the limit.
- B: all even moments to second order, `|t^k⟨x^{2k}⟩ − (2k−1)‼/λ^k − C_k/(λ^k t)| ≤ K/t²`,
  `C_k = (A²/2)((2k+5)‼ − 15(2k−1)‼) − B((2k+3)‼ − 3(2k−1)‼)`.
- C (optional): the even `O(1/t)` corollary.

## GPT-6 Astra v1

Saved verbatim in `gpt_moments_sharp_v1.md`. Summary: A and B correct (constants checked: `C₁ = 45A² − 12B`, `C₂ = 450A² − 96B`;
`C₀ = 0` with Lean's `(2·0 − 1)‼ = 0‼ = 1`); the odd remainder after `√t` is `O(t^{-3/2})`, ample for A. Normalise indices with
`omega` (`2k+4 = 2(k+2)`, `2(k+2) − 1 = 2k+3`), wrap the Gaussian moment lemma once and prove shifted evaluations from it; keep the
double factorials opaque (no recurrence needed); real differences, not ℕ subtraction. Keep the public odd constant as `λ^{k+2}` (the
`λ = s²` substitution is fine internally). Implement B first. Vote: A+B, C optional.

## Vote
- Claude: A+B
- GPT-6 Astra: A+B

## Numerical check

`numcheck_moments_sharp.py` (`λ = 2`, `a = ½`, `γ = λ²`, `t = 50 … 800`): `t·(t^{k+1}⟨x^{2k+1}⟩ − limit)` for `k = 0..3` converges to
`0.180, 0.772, 3.96, 23.7` (limits `−0.1768, −0.4419, −1.5468, −6.9606 = −α(2k+3)‼/(6λ^{k+2})`); `t²·(t^k⟨x^{2k}⟩ − (2k−1)‼/λ^k −
C_k/(λ^k t))` for `k = 1..3` converges to `−0.199, −1.60, −13.2`; `C₁ = −0.1875 = 45A² − 12B`, `C₂ = −0.875 = 450A² − 96B`.
