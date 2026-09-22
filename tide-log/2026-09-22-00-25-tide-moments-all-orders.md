# Tide: moments-all-orders

**Direction (user):** auto mode on the Sanity-on-Sampling note; the Laplace scaling of all moments of the exact anharmonic Gibbs measure,
`√(λt)^n ⟨xⁿ⟩ → E[gⁿ]` (Gaussian moments), by dominated convergence of the rescaled integrals `J_n`; the even/odd forms and the degree-5/6
bounds that E2's fourth prediction (`Cov[K, ψ]`, eq:covK) will need.
**Seabed:** laplace, commit 34954be (main)
**Started:** 2026-09-22T00:25Z

## Candidates v1 (Claude)

See `gpt_moments_all_orders_prompt_v1.md` (A–C verbatim).

- A: `tendsto_J_n : J_n(t) → ∫ uⁿ e^{−u²/2}` for every `n`, by dominated convergence with the seabed's `t`-uniform Gaussian bound.
- B: `√(λt)^n ⟨xⁿ⟩ → (∫ uⁿ e^{−u²/2})/√(2π)`; even `t^k⟨x^{2k}⟩ → (2k−1)‼/λ^k`, odd `√(λt)^{2k+1}⟨x^{2k+1}⟩ → 0`.
- C: `t²⟨x⁵⟩ → 0`, `t²⟨x⁶⟩ → 0`, `t³⟨x⁶⟩ → 15/λ³`, eventual boundedness.

## GPT-6 Astra v1

Saved verbatim in `gpt_moments_all_orders_v1.md`. Summary: A → B → C is the right chain; use dominated convergence (eventually in `t > 0`,
measurability separately, dominate the whole Boltzmann factor by `|u|ⁿ e^{−c₀u²}`), not the `K/t` rate machinery — a rate-based generalisation
would meet parity (`J_{2k} − G_{2k} = O(1/t)` but `J_{2k+1} = O(t^{-1/2})`); the pointwise limit has no subtlety. B: `sⁿ I_n/I_0 = J_n/J_0` with
`s = √(λt) ≠ 0`, state the core theorem with `Real.sqrt (lam * t) ^ n` (natural powers), even specialisation `t^k⟨x^{2k}⟩ → (2k−1)‼/λ^k`. C: keep
the Gaussian-scale odd limit `√(λt)^{2k+1}⟨x^{2k+1}⟩ → 0` (the sharper `t^{k+1}⟨x^{2k+1}⟩ → −α(2k+3)‼/(6λ^{k+2})` is a separate first-order
theorem, unnecessary for covK); `t²⟨x⁵⟩ = λ^{-5/2} t^{-1/2} S₅(t) → 0`, `t²⟨x⁶⟩ → 0` from `t³⟨x⁶⟩ → 15/λ³`. Vote: A+B+C.

## Vote
- Claude: A+B+C
- GPT-6 Astra: A+B+C

## Numerical check

`numcheck_moments_all_orders.py` (`λ = 2`, `a = ½`): `t^{n/2}⟨xⁿ⟩ → 0.5, 0.75, 1.875, 6.5625 = (n−1)‼/λ^{n/2}` for `n = 2, 4, 6, 8` to three
digits at `t = 1000`; odd `t^{(n+1)/2}⟨xⁿ⟩` converge to finite constants, so `√(λt)^n⟨xⁿ⟩ → 0` for odd `n`.

## Result

Commit `78c6e7b` on `tide/moments-all-orders`; `lake build` clean, `scripts/sorries` 0/0/0/0.
`Laplace/OneD/MomentsAllOrders.lean` (     183 lines): `tendsto_rescaledPerturbation`, `tendsto_J_n`, `sqrt_pow_mul_moment_eq`,
`moment_anharmonic_asymptotic`, `evenMoment_anharmonic_asymptotic` (+`'`), `oddMoment_anharmonic_tendsto_zero`,
`sixthMoment_anharmonic_asymptotic`, `sixthMoment_t_sq_tendsto_zero`, `fifthMoment_t_sq_tendsto_zero`.

Surprises: one dominated-convergence theorem replaces four bespoke asymptotic proofs (the seabed's `rescaled_boltzmann_decay` was
already the right uniform bound); the whole file compiled on the third round with only bookkeeping fixes.
