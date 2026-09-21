# Tide: per-direction closures of E1–E3

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." (auto run on the Sanity on Sampling mathematics; this tide closes two per-eigendirection statements of the note: the finite-chain shortfall is controlled by `τ_flat/(CN)`, and the localised LLC in the eigenbasis with the relative localisation `γ_rel`.)
**Seabed:** laplace, `main` at e620326; worktree `laplace-tide-direction-closures`, branch `tide/direction-closures`
**Started:** 2026-09-21 (UTC, see file name)

## Context

Section 2 of the note: along eigendirection `i` the ULA chain is AR(1) with `ρᵢ = 1 − lr pᵢ`, integrated autocorrelation time
`τᵢ = (1 + ρᵢ)/(1 − ρᵢ) ≈ 2/(lr pᵢ)`, `τ_flat = 2/(lr p_min)` ("`20κ` steps at `lr p_max = 0.1`"), and the finite-chain prediction for the
expected pooled sample variance (tide `sanity-chain-forms`: `pooled_sample_variance`, and its ULA realisation
`expected_pooled_sample_variance_ula`). E3: `γ_rel = γ/(tλ_min)` "how much `γ` stiffens the flattest direction"; the centred localised LLC
`½ ∑ᵢⱼ (tH)ᵢⱼ((tH+γ)⁻¹)ᵢⱼ` (tide `localised-bias`).

## Candidates v1 (Claude)

**A. Two closures.**

1. **Shortfall bound.** For `C` chains of an AR(1) process in an inner product space (`AR1Chain E ρ v`, mutually orthogonal noise),
   `0 ≤ ρ < 1`, `0 < v`, `σ² = v/(1 − ρ²)`, burn-in `b`, `N` draws:
   `pooledVar ≤ σ²` and `σ² − pooledVar ≤ σ² (ρ^{2(b+1)}/(N(1 − ρ²)) + (1 + ρ)/((1 − ρ) C N))`,
   from the closed form: `R₂ = ρ^{2(b+1)} ∑_{i<N} (ρ²)^i ≤ ρ^{2(b+1)}/(1 − ρ²)`, `T_N = N + 2∑_{m<N}(N − m − 1)ρ^{m+1} ≤ N(1 + ρ)/(1 − ρ)`, and
   `T_N − R₁² ≥ 0` (it is `‖∑ x‖²/σ²`, `norm_sum_window_sq`). The second term is exactly the note's `τᵢ/(CN)` with `τᵢ = (1+ρᵢ)/(1−ρᵢ)`.
   ULA realisation (`ρ = 1 − hp`, `0 < hp < 1`, `σ² = 1/(p(1 − hp/2))`): the expected pooled variance along a unit eigenvector `u` of `Q`
   falls short of the ULA law by at most `σ² ((1−hp)^{2(b+1)}/(N(1−(1−hp)²)) + 2/(h p C N))` — `τ_flat = 2/(h p_min)` as a bound
   (`expected_pooled_sample_variance_ula_shortfall`).
2. **Eigenbasis LLC.** `∑ᵢⱼ (tH)ᵢⱼ ((tH + γ)⁻¹)ᵢⱼ = ∑ᵢ tλᵢ/(tλᵢ + γ)` (`H.PosDef`, `t > 0`, `γ ≥ 0`; spectral decomposition `H = UΛUᵀ`, so
   `(tH + γ)⁻¹ = U (tΛ + γ)⁻¹ Uᵀ` and the double sum is a trace), hence `localised_llc_centred_eigen`:
   `t⟨½wᵀHw⟩ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)` for the centred localised Gaussian; and along an eigenvector `u` (`Hu = λu`),
   `uᵀ(tH + γ)⁻¹u = ‖u‖²/(tλ + γ) = (‖u‖²/(tλ)) / (1 + γ_rel)` with `γ_rel = γ/(tλ)` (`eigen_direction_variance`).

Rationale: the two formulas the note uses to reason about budgets (`τ_flat`, `20κ`) and localisation (`γ_rel`); both are corollaries of landed
tides plus elementary sums and the spectral packaging already in `Lyapunov.lean`/`ULA.lean`. Closed forms as stated (numerical check below).

**B. The statistical error of the estimator** (E4's `√(d/(CN))`): needs fourth moments of the chain (Gaussian process), a separate tide.

**C. Only 2** — too thin.

Claude's preference: A.

## Numerical check

`scratchpad/numcheck19.py`: `(ρ, N, C, b) = (0.99, 1000, 4, 100)`: shortfall `0.0511 ≤` bound `0.0564` (`τ/(CN) = 0.0500`);
`(0.999, 2000, 16, 0)`: `0.2689 ≤ 0.3121`; `(0.9, 50, 1, 5)`: `0.3269 ≤ 0.4097`; shortfall nonnegative in all cases. Eigenbasis LLC for a random
`4×4` PD `H`, `t = 3`, `γ = 1.5`: `½ tr(tH(tH+γ)⁻¹) = 1.6749081104 = ½ ∑ tλᵢ/(tλᵢ + γ)`.

## GPT-6 Astra v1

Saved verbatim in `gpt_direction_closures_v1.md`. Summary: (a) the shortfall bound is correct (`σ² − pooled = σ²(R₂/N + (T_N − R₁²)/(CN²))`
exactly, then the two elementary bounds; `T_N − R₁² ≥ 0` from `norm_sum_window_sq` with the witness chain `X ⟨0, hC⟩`); `(1+ρ)/(1−ρ)` is
exactly the stationary integrated autocorrelation time (`1 + 2∑_{k≥1} ρ^k`); tightness qualified: `Nτ − T_N = 2ρ(1−ρ^N)/(1−ρ)²`, so the bound is
leading-order sharp as `N → ∞` at fixed `ρ, b, C` but loose when `N(1−ρ)` is small; for ULA `τ = (2 − hp)/(hp) ≤ 2/(hp)`. (b) the eigenbasis
identity and `‖u‖²/(tλ+γ) = (‖u‖²/(tλ))/(1 + γ/(tλ))` for any eigenvector (normalised directional variance divides by `‖u‖²`; the note's
`γ_rel` uses `λ_min`, the per-direction version `λᵢ`). Lean: `geom_sum_eq` + `div_le_iff₀`, termwise `(N − m − 1)ρ^{m+1} ≤ Nρ^{m+1}`; prove the
diagonal affine identity entrywise; control association around `Uᵀ U` explicitly; `trace_mul_cycle`; nothing measure-theoretic is needed for
the ULA corollary. Votes **A** with the tightness wording corrected and the `2/(hp)` (`20κ`) corollary.

## Vote
- Claude: candidate A (with the ULA `τ_flat = 2/(hp)` corollary)
- GPT-6 Astra: candidate A (same)

Agreed.
