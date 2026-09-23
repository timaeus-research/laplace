# Context: laplace seabed, tide 113 (growing window)

Setting (tides 108–112, all formalised): ULA on the anchored Gaussian model at `h = η/t`, `0 < ηλᵢ < 2`, `αᵢ = 1−ηλᵢ`, `aᵢ = 1−ηλᵢ/2`, from a fixed
start `x₀`; burn-in schedule `k(t)` with `k(t) → ∞` and `t·r^{2k(t)} → 0` for some `r ∈ (maxᵢ|αᵢ|, 1)` (e.g. `⌈κ log t⌉`, `κ > 1/(2 log(1/r))`).
Formalised: the exact non-stationary autocovariance `Cov(q(X_s), q(X_{s+ℓ})) = ½∑λᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑λᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}`
(`v_{s,i} = σᵢ²(1−ρᵢ^{2s})`, `μ_{s,i} = m̂ᵢ + ρᵢ^s(x̂₀ᵢ−m̂ᵢ)`); the kernel-level `avgVar(k, n) = (1/n²)(∑_{a<n}Cov(k+a,0) + 2∑_{j<n}∑_{a<n−(j+1)}Cov(k+a, j+1))`;
for fixed `n`, `t²avgVar(k(t), n) → W_{η,n} = ½∑aᵢ⁻²F_n(αᵢ²)`, `n·F_n(z) = (1+z)/(1−z) − 2z(1−z^n)/(n(1−z)²)` (exact), and `n·W_{η,n} ↑ L_η = ∑(1+αᵢ²)/(4ηλᵢaᵢ³)`.
Also `t·E_{k(t)}q − t⟨L⟩_loc → b_η = (η/4)∑λᵢ/aᵢ` for any such schedule.

# Candidate (single theorem, growing window)

For ANY window `n : ℝ → ℕ` with `n(t) → ∞` (no relation to `t` required):
  (i)  `n(t)·t²·avgVar(k(t), n(t)) → L_η`;
  (ii) `(1/n(t))∑_{a<n(t)}(t·E_{k(t)+a}q − t⟨L⟩_loc) → b_η` (the scaled bias of the average, uniformly over the window);
  (iii) hence the scaled MSE of the growing-window average, `t²avgVar + (t·avgBias)²`, tends to `b_η²`: the error of a long-window average is
        dominated by the step-size bias, and the variance vanishes at the rate `L_η/(n t²)`.

Proof plan for (i) (no termwise uniform-in-lag lemma): write `n t² avgVar = (1/n)[∑_a Cq(k+a,0) + 2∑_j∑_a Cq(k+a,j+1)] + (mean part)`, with
`Cq(s,ℓ) = ½∑λᵢ²(tv_{s,i})²ρᵢ^{2ℓ}`. Sandwich: for `s ≥ k`, `(tσᵢ²)²(1−r^{2k})² ≤ (tv_{s,i})² ≤ (tσᵢ²)²` (even powers `ρ^{2ℓ} ≥ 0`), so the quadratic part lies
between `(1−r^{2k})²·Q` and `Q`, `Q := ½∑λᵢ²(tσᵢ²)²·n·F_n(ρᵢ²)`, and by the exact `n·F_n(z) = (1+z)/(1−z) − 2z(1−z^n)/(n(1−z)²)` with `z = ρᵢ(t)² → αᵢ²`,
`n(t) → ∞`: `Q → ½∑λᵢ²(aᵢλᵢ)⁻²(1+αᵢ²)/(1−αᵢ²) = L_η`; `(1−r^{2k(t)})² → 1`; squeeze. Mean part: `|tμ_sμ_{s+ℓ}| ≤ t(|m̂| + r^k|d|)² =: M(t) → 0`
uniformly in `s ≥ k`, so `|mean part| ≤ ∑λᵢ²(tσᵢ²)M(t)(1 + 2∑_{j<n}r^{j+1}) ≤ ∑λᵢ²(tσᵢ²)M(t)(1+2r/(1−r)) → 0`.
For (ii): `t·E_sq − t·L = BIAS_t − Burn(t,s) − C₁′/t − residual_s` with `|residual_s| ≤ K/t²` (budget, uniform in `s ≥ 1`) and `|Burn(t,s)| ≤ ½∑λ(tσ²)r^{2k} +
½∑λ(t r^{2k})d² + ∑λ|tm̂|r^k|d|` uniformly for `s ≥ k`, so the average of `n(t)` such terms → `b_η`.

Numerical check (`n(t) = ⌈√t⌉`, `κ = 1.5κ_crit`): `n t² avgVar → L_η = 6.1694` (values 4.63/5.75/6.09/6.15 at t = 10²…10⁵ — slow because `n·W_n − L_η = O(1/n)`),
`t·avgBias → b_η = 0.4469`, `t²MSE → b_η² = 0.1997`.

# Questions
1. Is the candidate correct as stated — in particular that no relation between `n(t)` and `t` is needed (only `n(t) → ∞`), and that the sandwich
   `(1−r^{2k})²Q ≤ quadratic part ≤ Q` is valid (we use `ρ^{2ℓ} ≥ 0` and `0 ≤ ρ_i^{2s} ≤ r^{2k}` for `s ≥ k`)? Is `L_η` here exactly tide 103's long-run variance?
2. Is there a cleaner route, or a stronger/cheaper statement (e.g. an explicit `O(1/n + ε(t))` rate; a statement for the MC error `√(L_η/n)/t` of the
   LLC estimator from one chain; the `C` chains × `N` draws version)? Anything wrong with (iii)'s reading "long windows are bias-dominated"?
3. Wording for the note (E4: "the covariance error follows √(d/(CN)) with a prefactor set by the autocorrelation times" and E5's long-run variance).
Vote please.
