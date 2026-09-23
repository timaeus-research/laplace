# Context: Lean formalisation of the "Sanity on Sampling" note (laplace seabed), tide 110

ULA on the anchored Gaussian model at inverse temperature `t`: precision `P_t = tH + gI`, `H = Q diag(λ) Qᵀ`, step `h = η/t` with `0 < ηλᵢ < 2`,
`ρᵢ = 1 − h(tλᵢ + g) → 1 − ηλᵢ`, started at a fixed `x₀`. The `k`-step law is Gaussian with covariance `Σ(1 − A^{2k})` and mean
`m + A^k(x₀ − m)` (frame: `m̂ᵢ = gŵᵢ/(tλᵢ+g)`, `σᵢ² = 1/(pᵢ(1 − hpᵢ/2))`). The statistic is `q(u) = ½uᵀHu` (the LLC statistic). Already formalised:

- (tide 105) `t²Var_k(q) = (t²/2)∑ᵢ(λᵢvᵢ)² + t²∑ᵢvᵢ(λᵢ(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ)))²`, `vᵢ = σᵢ²(1 − ρᵢ^{2k})`.
- (tide 108) along `k(t) = ⌈κ log t⌉₊` with `κ > 1/(2 log(1/r))`, `r ∈ (maxᵢ|1−ηλᵢ|, 1)`: `t⟨q⟩_{k(t)} − t⟨L⟩_loc → b_η := (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`,
  where `⟨L⟩_loc` is the exact localised Gibbs expectation of the anharmonic loss (the budget `t⟨L⟩_loc − t⟨q⟩_k = C₁′/t − (th/4)∑λᵢ/κᵢ + Burn_k + O(t⁻²)`).
- (tide 103) the stationary single-sample scaled variance `t²Var_∞(q) → V_η := ½∑ᵢ(1−ηλᵢ/2)⁻²`.
- (tide 102) linearity lemmas `⟨φ + c⟩ = ⟨φ⟩ + c`, `⟨q(f + c)⟩ = ⟨qf⟩ + c⟨q⟩` for the tilted Gaussian with shifted-integrability hypotheses, and
  integrability of `q`, `q²` (shifted) against the centred Gaussian.

# Candidates

A. `⟨(q − a)²⟩ = (⟨q²⟩ − ⟨q⟩²) + (⟨q⟩ − a)²` for any PD precision, tilt and Hermitian `H` (bias–variance decomposition).
B. Along any schedule with `k(t) → ∞` and `t·r^{2k(t)} → 0`: `t²Var_{k(t)}(q) → V_η`. Proof sketch: `(t²/2)∑(λᵢvᵢ)² = ½∑((tσᵢ²)λᵢ(1−ρ^{2k}))² → ½∑(1/(1−ηλᵢ/2))²`
   via `tσᵢ² → 1/(λᵢ(1−ηλᵢ/2))`; the mean term `t²∑vᵢλᵢ²(m̂ᵢ + ρ^k dᵢ)² = ∑(tσᵢ²)(1−ρ^{2k})λᵢ²[(tm̂ᵢ)m̂ᵢ + 2(tm̂ᵢ)ρ^k dᵢ + (tρ^{2k})dᵢ²] → 0`.
C. Specialisation to `k(t) = ⌈κ log t⌉₊`, `κ > 1/(2 log(1/r))`.
D. `t²⟨(q − ⟨L⟩_loc)²⟩_{⌈κ log t⌉} → b_η² + V_η` (from A, C and tide 108).
E. `η ↦ b_η² + V_η` is increasing on `(0, 2/λ_max)`.

Numerical check (d = 3, λ = (1, 2.5, 0.7), η = 0.3, κ = 1.5κ_crit): `t²Var_k → 2.5962 = V_η`, `t·bias → 0.4469 = b_η`, `t²MSE → 2.7960 = b_η² + V_η`
(2.7961 at t = 10⁶).

# Questions

1. Are A–E correct as stated? In B, is the hypothesis `t·r^{2k(t)} → 0` genuinely needed for the *variance* (through the mean-memory term
   `t·ρ^{2k}(x̂₀ − m̂)²`), or is there a slicker route needing only `k → ∞`? Is `⟨q⟩_k − ⟨L⟩_loc` (exact localised anharmonic expectation) the right
   centre for the "MSE" in D, given that the note's target is the LLC `d/2`-type quantity — should we also record the MSE against the Gaussian
   (harmonic) value `½tr(tH P_t⁻¹) + ½m̂ᵀHm̂`, which differs by `C₁′/t`?
2. Which is the strongest bundle for one tide, and what cheap additions are we missing? Candidates: (i) the MSE of the `n`-draw average after burn-in
   would need the non-stationary autocovariances `Cov(q(X_k), q(X_{k+ℓ}))` from a fixed start — is there a short route through the stationary
   autocovariance plus a burn-in correction that is `o(1)` at the log schedule? (ii) a statement that `b_η² + V_η` is minimised as `η → 0` while
   `κ_crit(η) → ∞`, i.e. the step size trades single-draw error against burn-in length; (iii) the value of `κ` at which the *transient* of the
   variance term `ρ^{2k}` is `o(1/t)` (needs `κ > 1/(2 log(1/r))` again?).
3. How should the note phrase D — is "after ⌈κ log t⌉ steps a single ULA draw estimates the localised energy with scaled root-mean-square error
   √(b_η² + V_η), i.e. the LLC statistic is O(1) accurate on the scale of `t⁻¹`" fair, and what caveats (Gaussian anchored model, exact gradients,
   fixed start, `η = ht` fixed) must accompany it?

Please give a vote: which candidates to formalise now.
