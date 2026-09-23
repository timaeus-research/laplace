# Tide: burnin-nonzero-start

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: E4's ULA burn-in law from an *arbitrary* start `x₀` on the Gaussian target (tide 92 treated the start at the mode): the k-step law `N((1 − hP)^k x₀, Σ_k)` as a tilted Gaussian, its Laplace transform (noncentral Gamma), mean energy with the geometric transient, per-mode bias sign, variance, and the stationary limits, via the tilted-Gaussian machinery of tides 92–97.
**Seabed:** laplace, commit 98c4e55 (tide 97 `anchored-covariance-gap` landed)
**Started:** 2026-09-23T04:34Z

## Candidates v1 (Claude)

`pᵢ` eigenvalues of `P ≻ 0`, `ρᵢ = 1 − hpᵢ`, `aᵢ = 1 − hpᵢ/2`, `fᵢ = 1 − ρᵢ^{2k}`, `Σ_k = ulaCov·(1 − ulaStep^{2k}) = U diag(fᵢ/(pᵢaᵢ)) Uᵀ`, start `x₀`, `bᵢ = (Uᵀx₀)ᵢ`, `m_k = (1 − hP)^k x₀`; the k-step law from `x₀` is `tiltedExpectation Σ_k⁻¹ (Σ_k⁻¹ m_k)` (k ≥ 1).
- **A** `burnIn_mean_start`: `⟨½uᵀPu⟩_k = ½∑ᵢfᵢ/aᵢ + ½∑ᵢpᵢρᵢ^{2k}bᵢ²`; `burnIn_bias_start`: `⟨½uᵀPu⟩_k − ½∑1/aᵢ = ½∑ᵢρᵢ^{2k}(pᵢbᵢ² − 1/aᵢ)`.
- **B** `burnIn_var_start`: `Var_k(½uᵀPu) = ½∑ᵢ(fᵢ/aᵢ)² + ∑ᵢpᵢρᵢ^{2k}bᵢ²·fᵢ/aᵢ`.
- **C** `laplace_ulaBurnIn_start`: for `s ≥ 0`, `⟨e^{−s·½uᵀPu}⟩_k = exp(−½∑ᵢ s pᵢaᵢρᵢ^{2k}bᵢ²/(aᵢ + s fᵢ))·√∏ᵢaᵢ/(aᵢ + s fᵢ)` (noncentral Gamma(½), noncentrality `δᵢ = pᵢaᵢρᵢ^{2k}bᵢ²/fᵢ`).
- **D** `burnIn_transient_tendsto`, `burnIn_mean_start_tendsto`: the transient `∑pᵢρᵢ^{2k}bᵢ² → 0` and the mean → `½∑1/aᵢ`.

## Numerical check

`numcheck_burnin_nonzero_start.py` (random 3×3 `P`, `h = 0.05`, `x₀ = (1.2, −0.7, 0.4)`, `k = 4`, `s = 0.7`, 4·10⁵ chains): chain mean/cov match `m_k`, `Σ_k` (errors 1e-3); mean energy MC 1.5979 vs 1.60067 (matrix = eigen), bias −0.21108 both forms; variance MC 1.8469 vs 1.84538; transform MC 0.4366 vs 0.43571 (matrix = eigen). Mean along k: 2.173 (k = 1, above the stationary 1.812) → 1.601 (k = 4) → 1.757 (k = 32): a hot start overshoots and then approaches from below.

## Questions for GPT-6 Astra (prompt in `gpt_burnin_nonzero_start_prompt_v1.md`)

Correctness of A–D and the noncentrality identification; E4 reading (hot vs cold start, non-monotone approach, "wait until the energy stabilises"); Lean route (reuse `burnIn_mean` for the trace, `laplace_ulaBurnIn` for the determinant ratio, `tiltedVar_quadForm`, eigen exponent); cheap additions; vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_burnin_nonzero_start_v1.md`)

- A–D correct under `h > 0`, `pᵢ > 0`, `hpᵢ < 2` (so `|ρᵢ| < 1`, `aᵢ > 0`, `fᵢ > 0` for `k ≥ 1`). Correction to A's prose claim: `pᵢbᵢ² = 1/aᵢ` for all
  `i` is sufficient but not necessary for the bias to vanish at every `k ≥ 1`; the exact condition is `∑_{i: ρᵢ² = r}(pᵢbᵢ² − 1/aᵢ) = 0` for
  every `r > 0` (modes with equal `ρᵢ²` can cancel; modes with `ρᵢ = 0` are unconstrained). Adopted in prose; the Lean statement is the
  signed sum, which is exact.
- Noncentrality read in the eigenbasis: mode `i` is `(wᵢ/2)χ²₁(δᵢ)`, `wᵢ = fᵢ/aᵢ`, `δᵢ = λᵢ/wᵢ = pᵢaᵢρᵢ^{2k}bᵢ²/fᵢ`, `λᵢ = pᵢρᵢ^{2k}bᵢ²`; cleaner
  transform `∏(1 + swᵢ)^{−1/2}exp(−(s/2)∑λᵢ/(1 + swᵢ))` (equivalent; extends to `k = 0`); "scaled noncentral χ²₁" is the safer terminology.
- E4 reading: hot modes make positive bias possible but the weighted sum decides; all `cᵢ ≤ 0` ⇒ monotone from below, all `cᵢ ≥ 0` ⇒ monotone
  from above, mixed signs ⇒ overshoot/cancellation (explicit example `r = (¼, 1/16)`, `c = (−1, 8)`: `B₁ = ⅛`, `B₂ = −1/64`). Wording for the
  note adopted (cold start at the mode; transient competes with covariance growth; "energy stabilisation is a diagnostic, not a
  certificate"); distinguish the start bias from the ULA discretisation bias `½∑(1/aᵢ − 1)`; pretrained weights are a mode start only if
  they are a stationary point of the actual sampling objective; exact ULA, no minibatch noise.
- Lean route endorsed (reuse `burnIn_mean` for the trace, `laplace_ulaBurnIn` for the determinant ratio, `tiltedVar_quadForm`); pitfalls
  listed (nonzero facts early, PosDef of `Q_k` and `Q_k + sP`, `k ≥ 1`, explicit matrix association, `(ρ^k b)² = ρ^{2k}b²` as a scalar step).
- Cheap additions: `k = 0` point mass, `Σ_{k+1} − Σ_k = 2hA^{2k} ⪰ 0`, stationary variance limit `½∑1/aᵢ²`, geometric bias bound
  `|B_k| ≤ ½R^k∑|cᵢ|`; pooled independent chains give `∑(wᵢ/(2M))χ²_M(Mδᵢ)`; time pooling is correlated — defer. Taken: variance limit and
  the geometric bound.

## Vote
- Claude: A–D plus `burnIn_var_start_tendsto` and `burnIn_bias_start_le`; `k = 0`, covariance monotonicity and pooling deferred
- GPT-6 Astra: land A–D with the corrected bias statements, prioritise mean/bias and transform, add variance and cheap limits, defer correlated time-pooling
