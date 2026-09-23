# Context: Lean formalisation of the "Sanity on Sampling" note (laplace seabed), tide 111

ULA on the anchored Gaussian model at inverse temperature `t`: precision `P_t = tH + gI`, `H = Q diag(λ) Qᵀ`, step `h = η/t`, `0 < ηλᵢ < 2`,
`ρᵢ(t) = 1 − h(tλᵢ+g) → αᵢ := 1 − ηλᵢ`, `aᵢ := 1 − ηλᵢ/2`, started at a fixed `x₀`. The `s`-step law is Gaussian with frame variances
`v_{s,i} = σᵢ²(1 − ρᵢ^{2s})`, `σᵢ² = 1/(pᵢ(1 − hpᵢ/2))`, and means `μ_{s,i} = m̂ᵢ + ρᵢ^s(x̂₀ᵢ − m̂ᵢ)`, `m̂ᵢ = gŵᵢ/(tλᵢ+g)`. Statistic `q(u) = ½uᵀHu`.
Formalised so far: (tide 102) the stationary autocovariance defined at kernel level as `Cov_π(q, condEnergy_ℓ)`, `condEnergy_ℓ(x) = E[q(X_ℓ)|X_0 = x]
= ½xᵀB_ℓx + b_ℓ·x + c_ℓ` (quadratic in `x`), with Wick covariance lemmas for `Cov(½uᵀHu, ½uᵀBu + u·b)` under any tilted Gaussian; (tide 105) the
`k`-step variance; (tide 108) `t⟨q⟩_{⌈κ log t⌉} − t⟨L⟩_loc → b_η = (η/4)∑λᵢ/aᵢ`; (tide 110) `t²Var_{⌈κ log t⌉}(q) → V_η = ½∑aᵢ⁻²` and the single-draw
MSE `→ b_η² + V_η`. Your previous advice (tide 110): the exact non-stationary formula
`Cov(q(X_s), q(X_{s+ℓ})) = ½∑λᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑λᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}`, and for fixed `n` post-burn-in draws the limiting scaled MSE
`b_η² + ½∑aᵢ⁻²F_n(αᵢ²)`, `F_n(z) = (n + 2∑_{ℓ=1}^{n−1}(n−ℓ)z^ℓ)/n²`.

# Candidates

A. `burnAutoCov(s, ℓ) := Cov_{law_s}(q, condEnergy_ℓ)` (kernel-level; `s ≥ 1`), closed form `½∑λᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑λᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}` for all `ℓ`
   (proof: tide 102's Wick lemma with `Σ = Σ_s`, `m = μ_s`, `B_ℓ`, `b_ℓ` in the frame; lag 0 is tide 105's variance).
B. Along a schedule with `k(t) → ∞`, `t·r^{2k(t)} → 0` (`r ∈ (maxᵢ|αᵢ|, 1)`), for each fixed `ℓ`: `t²·burnAutoCov(k(t), ℓ) → c_ℓ^∞ := ½∑aᵢ⁻²αᵢ^{2ℓ}`.
C. Tide 108's mean statement for a general schedule (to apply at `k(t) + a`).
D. `avgVar(k, n) := (1/n²)(∑_{a<n} burnAutoCov(k+a, 0) + 2∑_{j<n}∑_{a<n−(j+1)} burnAutoCov(k+a, j+1))`, `avgBias(k, n) := (1/n)∑_{a<n}(E_{k+a}q − ⟨L⟩_loc)`;
   `t²avgVar(k(t), n) → (1/n²)(n c₀^∞ + 2∑_{j<n}(n−(j+1))c^∞_{j+1}) = ½∑aᵢ⁻²F_n(αᵢ²)`, `t·avgBias → b_η`, and `t²avgVar + (t·avgBias)² → b_η² + ½∑aᵢ⁻²F_n(αᵢ²)`.
   The identification of `avgVar` with the true variance of `(1/n)∑_a q(X_{k+a})` and of the sum with the MSE is the prose Markov/tower bridge,
   as in tide 102.
E. `1/n ≤ F_n(z) ≤ 1` for `z ∈ [0, 1)`.

Numerical check: the closed form in A agrees with a Monte Carlo simulation of the chain (t = 50, s = 6, lags 0–4, 4·10⁵ paths) to the MC error;
`t²c_ℓ(k(t))` converge to `c_ℓ^∞`; for `n = 5`, `t²avgVar → 1.0107 = ½∑aᵢ⁻²F_5(αᵢ²)`, `t·avgBias → 0.4469`, scaled MSE → 1.2104 (d = 3, λ = (1, 2.5, 0.7), η = 0.3).

# Questions

1. Are A–E correct? In particular: (i) is `Cov_s(q, condEnergy_ℓ)` the right kernel-level object (with `condEnergy_ℓ` the conditional mean *from the
   state at time s*, so that `Cov(q(X_s), q(X_{s+ℓ})) = Cov_{X_s}(q, condEnergy_ℓ)` by the tower property), and does the closed form use
   `μ_{s+ℓ} = ρ^ℓμ_s + (1−ρ^ℓ)m̂` correctly? (ii) In B, is the memory term `t·λ²v_sρ^ℓμ_sμ_{s+ℓ}` really `o(1)` under `t·r^{2k} → 0` (we expand
   `tμ_sμ_{s+ℓ} = (tm̂)m̂ + (tm̂)(ρ^{s+ℓ} + ρ^s)d + (tρ^{2s})ρ^ℓd²`)? (iii) In D, is the double-sum bookkeeping of pairs `(a, a+j+1)` with `a+j+1 < n` right,
   and is `1/n ≤ F_n ≤ 1` the right sanity bound (`F_n(0) = 1/n`, `F_n(z) → 1` as `z → 1`)?
2. What is the strongest bundle and what cheap additions are missing? E.g. (i) `F_n(z) ≤ (1+z)/((1−z)n)` (the usual IAT bound, so the `n`-draw
   average has scaled MSE `≤ b_η² + (IAT-weighted) V_η/n`); (ii) monotonicity of `F_n` in `z` (positively correlated draws are worth less);
   (iii) the `n → ∞` limit `n·F_n(z) → (1+z)/(1−z)` recovering tide 103's `L_η` for the stationary long-run variance; (iv) a bias–variance split with
   `n` chains × `1` draw (independent replicas: `b_η² + V_η/n`).
3. How should the note phrase D — "after logarithmic burn-in, `n` consecutive draws estimate the localised energy with scaled MSE
   `b_η² + ½∑aᵢ⁻²F_n(αᵢ²)`, i.e. the variance is reduced by the factor `F_n(αᵢ²) ∈ [1/n, 1]` per mode; the bias `b_η` is not reduced by averaging" —
   fair, with what caveats?

Please give a vote: which candidates to formalise now.
