# Tide: growing-window

**Direction (user):** auto mode — E4/E5: the growing-window average after logarithmic burn-in: for any window `n(t) → ∞`, `n(t)·t²·avgVar(k(t), n(t)) → L_η` (the long-run variance emerges), the scaled bias of the average `→ b_η`, so the scaled MSE of the growing-window average `→ b_η²`.
**Seabed:** laplace, commit a1119d5 (tides 111 `BurnInAverage` (`avgVar`, `lagWeight`), 112 `LagWeightLongRun` (`mul_lagWeight_eq`), 108 `BurnInLog`)
**Started:** 2026-09-23-11-16 UTC

## Candidates v1 (Claude)

Setting as in tides 108–112 (anchored model, `h = η/t`, `0 < ηλᵢ < 2`, fixed start, burn-in schedule `k(t) → ∞` with `t·r^{2k(t)} → 0`,
`r ∈ (maxᵢ|αᵢ|, 1)`). For **any** window `n : ℝ → ℕ` with `n(t) → ∞` (no relation to `t`):

- **A** (`ulaAnchored_window_var_tendsto`): `n(t)·t²·avgVar(k(t), n(t)) → L_η`. Proof by sandwich: for `s ≥ k`,
  `(1−r^{2k})²(tσᵢ²)² ≤ (tv_{s,i})² ≤ (tσᵢ²)²`, so the quadratic part of the window variance lies between `(1−r^{2k(t)})²·winEnv` and `winEnv`,
  `winEnv = ½∑ᵢλᵢ²(tσᵢ²)²·n·F_n(ρᵢ²) → L_η` by tide 112's exact `n·F_n` at `z = ρᵢ(t)² → αᵢ²`; the mean (memory) part is bounded by
  `∑ᵢλᵢ²(tσᵢ²)·t(|m̂ᵢ| + r^k|dᵢ|)²·(1 + 2r/(1−r)) → 0` uniformly in the window.
- **B** (`ulaAnchored_window_bias_tendsto`): `(1/n(t))∑_{a<n(t)}(t⟨q⟩_{k(t)+a} − t⟨L⟩_loc) → b_η` (uniform burn-in envelope over `s ≥ k`).
- **C** (`ulaAnchored_window_mse_tendsto`): `t²·avgVar + (t·avgBias)² → b_η²`: long windows are bias-dominated at fixed `η`, the variance
  vanishing at the rate `L_η/(n(t)t²)`.

## Numerical check

`numcheck113.py` (`n(t) = ⌈√t⌉`, `κ = 1.5κ_crit`, `λ = (1, 2.5, 0.7)`, `η = 0.3`, `g = 0.7`):
```
L_eta=6.169411  b_eta=0.446895
  t=   1e+02 k= 15 n=  10  n t^2 avgVar = 5.52223   t*avgBias = 0.45792   t^2 MSE = 0.76192 -> b^2 = 0.19971
  t=   1e+03 k= 22 n=  32  n t^2 avgVar = 5.93007   t*avgBias = 0.44793   t^2 MSE = 0.38595 -> b^2 = 0.19971
  t=   1e+04 k= 30 n= 100  n t^2 avgVar = 6.08801   t*avgBias = 0.44696   t^2 MSE = 0.26066 -> b^2 = 0.19971
  t=   1e+05 k= 37 n= 317  n t^2 avgVar = 6.14338   t*avgBias = 0.44690   t^2 MSE = 0.21910 -> b^2 = 0.19971
```
(`n·W_n − L_η = O(1/n)`, so the convergence in `n` is slow but monotone; the bias and the MSE limit are sharp already at `t = 10³`.)

## GPT-6 Astra v1

Full response in `gpt_growing-window_v1.md` (prompt in `gpt_growing-window_v1_prompt.md`). Summary: **approve**. The sandwich is valid (even lag
powers, `0 ≤ ρᵢ^{2s} ≤ r^{2k}` for `s ≥ k`); the decisive point is the *uniform* estimate `|nF_n(ρᵢ²) − (1+ρᵢ²)/(1−ρᵢ²)| ≤ 2r²/(n(1−r²)²)`, which is why
no coupling between `n(t)` and `t` is needed. `L_η` is exactly tide 103's constant under the per-iteration, scaled-observable normalisation
(`Γ_η(0) + 2∑_{ℓ≥1}Γ_η(ℓ)` with `Γ_η(ℓ) = ½∑aᵢ⁻²αᵢ^{2ℓ}`). Part (ii) needs only eventual positivity of `n(t)`, and is best seen as
`sup_{s≥k(t)}|tE_sq − t⟨L⟩_loc − b_η| → 0`. Suggested (deferred) strengthening: quantitative bounds `|nt²avgVar − L_η| ≤ K(1/n + 1/t + tr^{2k})`
and `sup_n|avgBias − b_η| ≤ K(1/t + tr^{2k})` under `O(1/t)` parameter rates. Wording: distinguish the MC error of the *scaled* LLC estimator
(`SD(t·q̄) ∼ √(L_η/n)`) from the unscaled average (`√L_η/(t√n)`); for `C` chains × `N` draws the variance is `∼ L_η/(CNt²)` when `N(t) → ∞`
(`CN → ∞` alone does not justify `L_η`; fixed `N` gives `NW_{η,N}`); "bias-dominated" presumes `b_η ≠ 0`, i.e. fixed `η > 0`; RMS statements only,
no CLT.

## Vote
- Claude: A + B + C
- GPT-6 Astra: "yes—formalise the candidate. The strongest useful packaging is a uniform-in-n variance-error bound plus a uniform post-burn-in bias bound; the growing-window theorem then follows immediately."
