# Tide: ula-autocovariance

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: E5 — the stationary lag-`ℓ` autocovariance of the ULA-sampled anchored energy `Y = ½uᵀHu`, defined as the covariance under the stationary law `N(m, Σ)` between `Y` and its `ℓ`-step conditional mean (the seabed's burn-in law from a start), its closed form `½∑λᵢ²σᵢ⁴ρᵢ^{2ℓ} + ∑λᵢ²σᵢ²m̂ᵢ²ρᵢ^ℓ`, the long-run variance `τ² = c₀ + 2∑_{ℓ≥1}c_ℓ` with the integrated autocorrelation times `(1+ρᵢ²)/(1−ρᵢ²)` and `(1+ρᵢ)/(1−ρᵢ)`, and the exact finite-`n` variance of the chain average.
**Seabed:** laplace, commit be39b46 (tide 101 `minibatch-budget` landed)
**Started:** 2026-09-23T06:06Z

## Candidates v1 (Claude)

`pᵢ = tλᵢ + g`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2`, `σᵢ² = 1/(pᵢκᵢ)` (stationary ULA covariance `Σ = ulaCov P h = U diag(σ²) Uᵀ`), `m̂ = Uᵀm`, `A = 1 − hP = U diag(ρ) Uᵀ`. The stationary law is the tilted Gaussian with precision `Σ⁻¹` and tilt `Σ⁻¹m`; the `ℓ`-step law from a start `x₀` is the seabed's `burnInTiltAnch` Gaussian (tide 99).
- **A** (Multi). `condEnergy ℓ x₀ := ⟨½uᵀHu⟩_{ℓ-step law from x₀}` is the quadratic-plus-linear probe `½x₀ᵀB_ℓx₀ + b_ℓ·x₀ + c_ℓ` with `B_ℓ = (Aᵀ)^ℓHA^ℓ = U diag(λρ^{2ℓ}) Uᵀ`, `b_ℓ = U diag(λρ^ℓ(1−ρ^ℓ)) Uᵀ m` (`condEnergy_eq_probe`, from `burnInAnch_energy_frame`). Then `ulaAutoCov ℓ := Cov_{N(m,Σ)}(½uᵀHu, condEnergy ℓ u)` (tower property gloss: `Cov(Y₀, Y_ℓ)` of the stationary chain) has, for `ℓ ≥ 1`,
  `ulaAutoCov ℓ = ½∑ᵢλᵢ²σᵢ⁴ρᵢ^{2ℓ} + ∑ᵢλᵢ²σᵢ²m̂ᵢ²ρᵢ^ℓ` (`ulaAutoCov_eq`), via tide 97's mixed Wick `tiltedCov_quadForm_quadProbe` and new generic frame lemmas (`Cov(q, f + c) = Cov(q, f)`, `∑ₐ∑_c (UD₁Uᵀ)ₐ_c(UD₂Uᵀ)_cₐ = ∑d₁d₂`, `(UD₁Uᵀx)·(UD₂Uᵀ)(UD₃Uᵀy) = ∑d₁d₂d₃x̂ŷ`).
- **B** (Multi). Long-run variance: with `c₀ = ½∑λᵢ²σᵢ⁴ + ∑λᵢ²σᵢ²m̂ᵢ²` (tide 100's stationary variance) and `c_ℓ` the closed form, `τ² := c₀ + 2∑'_{ℓ≥1} c_ℓ = ½∑ᵢλᵢ²σᵢ⁴(1+ρᵢ²)/(1−ρᵢ²) + ∑ᵢλᵢ²σᵢ²m̂ᵢ²(1+ρᵢ)/(1−ρᵢ)` (`ulaLongRunVar_eq`; `tsum_geometric_of_abs_lt_one`), and the integrated autocorrelation times in sampler variables: `(1+ρᵢ)/(1−ρᵢ) = 2κᵢ/(hpᵢ)`, `(1+ρᵢ²)/(1−ρᵢ²) = (1+ρᵢ²)/(2hpᵢκᵢ)` — at the β-scaled step `h = η/t` these tend to `(2−ηλᵢ)/(ηλᵢ)`, `(1+(1−ηλᵢ)²)/(ηλᵢ(2−ηλᵢ))`: `t`-independent steps per effective sample.
- **C** (Multi). Exact finite-`n` variance of the chain average as an identity of the lag function: `(1/n²)(n c₀ + 2∑_{ℓ=1}^{n−1}(n−ℓ)c_ℓ) = (1/n²)∑ᵢ[½λᵢ²σᵢ⁴(n + 2G_n(ρᵢ²)) + λᵢ²σᵢ²m̂ᵢ²(n + 2G_n(ρᵢ))]` with `G_n(r) = ∑_{ℓ=1}^{n−1}(n−ℓ)r^ℓ = r(n(1−r) − (1−rⁿ))/(1−r)²` (`cesaro_geometric`, induction), so `Var(Ȳ_n) = τ²/n − O(1/n²)` with an explicit remainder.
- **D** (optional). β-scaled limit `t²τ² → ∑ᵢ ½(1+(1−ηλᵢ)²)/(ηλᵢ(2−ηλᵢ)(1−ηλᵢ/2)²)` (the mean part vanishes like `1/t`).

## Numerical check

`numcheck102.py` (2D anchored Gaussian, `t = 20`, `g = 0.7`, `h = 0.3/t`, rotated frame, 4·10⁶ chains): the closed form A agrees with the exact tilted-Gaussian covariance of the probe to 1e-16 and with Monte Carlo autocovariances at lags 0–8 to within MC error; the conditional mean equals the probe plus constant and tide 99's frame form; B's series and closed form agree; C's lag-sum, closed form and Monte Carlo agree.
```
lag  closed        exact-Gauss   MC
  0  4.842230e-03  4.842230e-03  4.841507e-03
  1  9.776172e-04  9.776172e-04  9.799182e-04
  2  3.904298e-04  3.904298e-04  3.871214e-04
  3  1.829112e-04  1.829112e-04  1.864474e-04
  4  8.798378e-05  8.798378e-05  9.012791e-05
  5  4.272658e-05  4.272658e-05  4.347540e-05
  6  2.094891e-05  2.094891e-05  2.555766e-05
  7  1.040043e-05  1.040043e-05  1.276611e-05
  8  5.249100e-06  5.249100e-06  7.279794e-06
cond mean 0.07122410195636412 probe+c 0.07122410195636412
tide99 form 0.07122410195636411
tau2 series 0.00829085854063125 closed 0.008290858540631248
integrated autocorr times (quad, lin): [2.81250301 1.12170132] [5.44122383 1.62984878]  1/(hp), 2/(hp): [3.22061192 1.31492439] [6.44122383 2.62984878]
Var(mean_n) lag-sum 3.214711e-04 closed 3.214711e-04 MC 3.198598e-04  tau2/n 3.316343e-04
```

## GPT-6 Astra v1

Verbatim in `gpt_ula_autocovariance_v1.md` (prompt in `gpt_ula_autocovariance_v1_prompt.md`). Summary:
- **A–C correct** (given the common frame, `|ρᵢ| < 1` and the *ULA* stationary covariance `Σ_h = ulaCov P h`, not `P⁻¹`). The cross and linear
  Wick terms merge already at matrix level: `B_ℓm + b_ℓ = A^ℓHm`; the `ρ^{2ℓ}` (quadratic part) vs `ρ^ℓ` (mean part) split is essential — the mean
  part can alternate in sign for `ρ < 0`. Define `condEnergy 0 = q` (do not represent the zero-step Dirac law by a nonsingular Gaussian) so the
  formula holds at all lags, the lag-0 value being the stationary variance. C is correct for `n ≥ 1` (the lag-`n` coefficient is 0); `G_n` is
  correct for `r ≠ 1`, also at `n = 0`.
- **Proxy**: "covariance under the stationary law between `q` and its `ℓ`-step conditional mean" is the standard kernel-level definition
  `c_ℓ = Cov_π(q, K^ℓq)`; for a stationary chain it equals `Cov(Y₀, Y_ℓ)` by conditioning. Suggested wording: "no path-space process or tower-property
  theorem is formalised here"; and the identification of the seabed's burn-in Gaussians with `K^ℓ` is a second unformalised bridge unless a kernel-
  iteration theorem exists. Call C the "lag-sum variance functional".
- **E5**: `Var(tȲ_n) = t²τ²/n + O(n⁻²)` for a fixed stable sampler (stationary Monte Carlo variance, not bias/burn-in). With `h = η/t`,
  `ρᵢ → 1 − ηλᵢ`; the integrated autocorrelation times are *asymptotically* `t`-independent (need `0 < ηλᵢ < 2`), and boundedness of `t²τ²` uses
  `m̂ᵢ = O(1/t)`. Be careful contrasting with burn-in (its contraction rate is also `t`-independent; burn-in grows only logarithmically in `t` from
  a fixed displacement). Compare with independent replicates under the *same* stationary law (`t²c₀/n`); the `d/2` baseline is the small-step limit.
  Factor 2: `(1+ρ)/(1−ρ) ~ 2/(ηλ)` (AR(1)) vs `(1+ρ²)/(1−ρ²) ~ 1/(ηλ)` (centred squared AR(1)); `τ²/c₀` is a variance-weighted average of the modewise IATs.
- **Lean**: covariance-shift lemma at the expectation layer (only `w, qw, fw, qfw` integrable + `E(1) = 1`); package the stationary-law conversion
  (`Q` PosDef, `Q⁻¹ = Σ_h`, `tiltMean Q (Qm) = m`); geometric series via `|ρ| < 1` (ρ may be negative), `|ρ²| < 1` by a helper; ℕ- vs ℝ-subtraction in
  `G_n`; normalise finite sums before `ring`.
- **Cheap additions**: lag-0 compatibility + summability; `τ² ≥ 0`; the exact finite-`n` correction `n + 2G_n(r) = n(1+r)/(1−r) − 2r(1−rⁿ)/(1−r)²`
  giving `Var(Ȳ_n) = τ²/n − (2/n²)∑ᵢ[aᵢρᵢ²(1−ρᵢ^{2n})/(1−ρᵢ²)² + bᵢρᵢ(1−ρᵢⁿ)/(1−ρᵢ)²]`. Defer D.
- **Vote: A+B+C.**

Adopted: `condEnergy 0 = q` by an `if`, all-lag `ulaAutoCov_eq`, `ulaAutoCov_summable`, `ulaLongRunVar_nonneg`, the finite-`n` correction
`lagSumVar_eq_longRun_sub`; the stationary-law package `ulaCov_posDef_frame`/`ulaCov_inv_inv_frame`/`tiltMean_statTilt`. The integrability of the
shifted product is still a generated 15-term tree (the seabed has no polynomial-growth integrability lemma; the generator makes it free).

## Vote
- Claude: A+B+C (+ the cheap additions)
- GPT-6 Astra: A+B+C

## Result

Commit `e79b206` on `tide/ula-autocovariance`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/ULAAutocovariance.lean` (     682 lines).
A–C as voted, plus GPT's cheap additions.
Sampler (tilted layer): `tiltedExpectation_add_const`, `tiltedExpectation_mul_add_const`, `tiltedCov_add_const`, `integrable_shift_energy`,
`integrable_shift_quadProbe`, `integrable_shift_energy_mul_quadProbe`, `tiltedCov_energy_quadProbe_add_const`.
Sampler (frame): `sum_range_cesaro_geometric`, `conj_diagonal_transpose_frame`, `isHermitian_conj_diagonal`, `sum_sum_conj_mul_conj`,
`dotProduct_conj_diagonal_mulVec₂`, `transpose_mulVec_conj_mulVec`, `conj_mulVec_dotProduct_conj_mulVec`, `ulaCov_posDef_frame`,
`ulaCov_inv_inv_frame`, `statTilt`, `tiltMean_statTilt`, `condEnergy`, `ulaAutoCov`, `ulaLongRunVar`, `lagSumVar`, `condEnergy_eq`,
`isHermitian_of_frame`, `ulaAutoCov_zero_eq`, `ulaAutoCov_eq_of_pos`, `ulaAutoCov_eq`, `abs_rho_lt_one`, `ulaAutoCov_summable`,
`ulaLongRunVar_eq`, `ulaLongRunVar_eq_sampler`, `ulaLongRunVar_nonneg`, `lagSumVar_eq`, `lagSumVar_eq_longRun_sub`.

Surprises: two build rounds. `Σ` is a reserved token (a hypothesis `hΣ` broke parsing), `ring` does not see `x^(2ℓ) = (x²)^ℓ` for a compound
base (`← pow_mul` first), and the E3 Wick lemmas live in `Laplace.Sampler` behind an import not in `ULAFluctuationBudget`'s closure. The
sampler-variable form of τ² needed the denominators rewritten into products of atoms before `field_simp`. Mathematically, the cross and linear
Wick terms merge per mode into a single `ρ^ℓ` term (GPT: `B_ℓm + b_ℓ = A^ℓHm` at matrix level), and at the β-scaled step the integrated
autocorrelation times `(1+ρ²)/(1−ρ²) → (1+(1−ηλ)²)/(ηλ(2−ηλ))`, `(1+ρ)/(1−ρ) → (2−ηλ)/(ηλ)` are t-independent: stationary sampling needs an
asymptotically t-independent number of steps for fixed precision (the check: 2.8/5.4 steps per effective sample vs 1/(hp) = 3.2, 2/(hp) = 6.4).
