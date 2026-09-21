# Tide: autocorrelation-time

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the integrated autocorrelation time of the AR(1) eigen-chain (Setup / E1).
**Seabed:** laplace, commit 183b092 (main, after `llc-mse`)
**Started:** 2026-09-21 (UTC, see filename)

## Context

The sanity note's Setup paragraph: "Along direction `i` the chain is an AR(1) process with coefficient `ρᵢ = 1 − lr pᵢ`, so its integrated
autocorrelation time is `τᵢ = (1 + ρᵢ)/(1 − ρᵢ) ≈ 2/(lr pᵢ)`: stiff directions decorrelate in a few steps, the flattest in
`τ_flat = 2/(lr pmin)` steps, which for a condition number `κ` and `lr pmax = 0.1` is `20κ` steps." E1: "at `κ = 1000` and `lr pmax = 0.01`
the flattest direction has `τ_flat = 2 × 10⁵` steps against 50 000 draws, so the chain has not spread out along it". The Summary: "the draw
budget in units of `τ_flat = 2/(lr pmin)`".

Seabed: `inner_ulaChain_eq_realChain` (the eigen-projection of the ULA chain is the AR(1) chain `realChain (1 − hp)` driven by
`projNoise`, white with variance `2h`: `integral_projNoise_mul`, mean zero `integral_projNoise`), the Gram table
`integral_realChain_mul_realChain` (`E[x_k x_l] = s₂ (ρ^{|k−l|} − ρ^{k+l})`, `s₂ = v/(1 − ρ²)`), the Toeplitz identity `sum_sum_pow_dist`
(`∑_{k,l<N} ρ^{|k−l|} = N + 2∑_{m<N} (N − m − 1) ρ^{m+1}`) and its bound `toeplitz_sum_le` (`≤ N(1+ρ)/(1−ρ)`), the variance-of-a-sum
identity `variance_sum_eq_sum_cov`, and `two_div_eq_twenty_kappa` (`2/(h pmin) = 20κ` at `h pmax = 1/10`). Nothing states the
autocorrelation time itself.

## Candidates v1 (Claude)

**A. The Toeplitz sum in closed form.** For `ρ ≠ 1`,
```
toeplitz_sum_eq : ∑_{k<N} ∑_{l<N} ρ^{|k−l|} = N (1+ρ)/(1−ρ) − 2ρ (1 − ρ^N)/(1−ρ)²
```
(via `sum_sum_pow_dist` and `∑_{m<N} (N − m − 1) ρ^{m+1} = ρ (N(1−ρ) − (1 − ρ^N))/(1−ρ)²`, by induction on `N`). Refines `toeplitz_sum_le`.

**B. The variance of the running mean of the zero-start AR(1) chain.** For `realChain ρ η` with white innovations of variance `v`
(`L²`, uncorrelated, mean zero), `x̄_N = (1/N) ∑_{k<N} x_{b+1+k}`:
```
integral_realChain_eq_zero    : E x_k = 0
variance_running_mean_realChain :
  Var x̄_N = (v/(1−ρ²))/N² · ( ∑_{k,l<N} ρ^{|k−l|} − (∑_{k<N} ρ^{b+1+k})² )
```
(the `ρ^{k+l}` part of the Gram table factorises as a square of a geometric sum).

**C. The integrated autocorrelation time.** For `0 ≤ ρ < 1`:
```
tendsto_toeplitz_div : (∑_{k,l<N} ρ^{|k−l|}) / N → (1+ρ)/(1−ρ)              (N → ∞)
iat_realChain        : N · Var x̄_N / (v/(1−ρ²)) → (1+ρ)/(1−ρ)                 (N → ∞)
```
i.e. `Var x̄_N ∼ s₂ τ/N` with `τ = (1+ρ)/(1−ρ)`: the definition of the integrated autocorrelation time as the variance inflation of the
sample mean, realised for the zero-start chain (the transient `(∑ ρ^{b+1+k})²/N` term vanishes in the limit).

**D. The note's numbers.** `iat_eq : (1 + (1−hp))/(1 − (1−hp)) = 2/(hp) − 1` for `hp ≠ 0` (so `τ ≈ 2/(lr p)` is `τ = 2/(lr p) − 1` exactly), and
`iat_flat_twenty_kappa : h pmax = 1/10 → pmin = pmax/κ → τ_flat = 2/(h pmin) − 1 = 20κ − 1`.

**E. The ULA instance.** For the eigen-projection `⟨uᵢ, x_k⟩` of the ULA chain for a symmetric precision `Q` with Gaussian noise,
`0 < h pᵢ < 2`: B and C hold with `v = 2h`, `ρ = 1 − h pᵢ`, `s₂ = 1/(pᵢ(1 − h pᵢ/2))` (`variance_running_mean_ulaChain`,
`iat_ulaChain`), so `N · Var(⟨uᵢ, x̄_N⟩) · pᵢ(1 − h pᵢ/2) → 2/(h pᵢ) − 1`.

Vote intention: A+B+C+D+E (E is the instantiation that makes the statement about the sampler of the note).

## Numerical check

`numcheck31.py` (`h = 0.5`, `p = 0.3`, `v = 2h`, `b = 5`; 40 000 Monte Carlo chains):
```
N=  10: toeplitz direct=62.652733 closed=62.652733 | Var(xbar) MC=2.104286 formula=2.110813 | N Var/s2=5.8575 -> tau=12.3333 = 2/(hp)-1=12.3333
N=  40: toeplitz direct=417.891285 closed=417.891285 | Var(xbar) MC=0.933222 formula=0.927001 | N Var/s2=10.2897 -> tau=12.3333 = 2/(hp)-1=12.3333
N= 200: toeplitz direct=2391.111111 closed=2391.111111 | Var(xbar) MC=0.215340 formula=0.214846 | N Var/s2=11.9239 -> tau=12.3333 = 2/(hp)-1=12.3333
tau_flat = 2/(h pmin) - 1 = 1999.0 = 20 kappa - 1 = 1999.0
```
The closed form is exact, the variance formula matches Monte Carlo, and `N Var/s₂` approaches `τ` from below (the zero-start transient).

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_autocorrelation_time_v1.md` (prompt in `gpt_autocorrelation_time_prompt_v1.md`). Summary: A (including `N = 0`), B, D correct; C needs `v > 0` (Lean's `x/0 = 0`) — already a hypothesis — and the transient correction in `N·Var/s₂` is `G_N²/N = O(1/N)` with `G_N = ρ^{b+1}(1−ρ^N)/(1−ρ)` bounded; E must not advertise `0 < hp < 2` (negative `ρ`): restrict to `hp ≤ 1` (as the Lean statement does) or extend C to `|ρ| < 1`. Terminology: `τ = 1 + 2Σ_{m≥1} ρ^m` is the *stationary* integrated autocorrelation time; the zero-start chain has the same asymptotic variance inflation but not the stationary finite-time correlations — say so. Lean: induction for A is dependable (cast to ℝ first); `MemLp.integrable_mul` for `L²·L²`; state the limits on `atTop : Filter ℕ` with identities proved eventually (`N ≥ 1`). Cheap additions: E1's exact instance `τ_flat = 199 999` (the note's `2×10⁵`); ESS `N/τ` only asymptotically.

## Vote
- Claude: A+B+C+D+E (E under `0 < hp ≤ 1`; the stationary/zero-start remark recorded here and in the SRI note)
- GPT-6 Astra: A+B+C+D+E

Agreed. Proceeding to Step 3.
