# Tide: autocov-scaled

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: tide 102's deferred candidate D — the β-scaled step `h = η/t` limits of the E5 quantities on the anchored quadratic model: the long-run variance of the scaled statistic `t²τ²(t) → ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`, the integrated autocorrelation times `→ (1+(1−ηλᵢ)²)/(ηλᵢ(2−ηλᵢ))`, `(2−ηλᵢ)/(ηλᵢ)`, the vanishing mean part, and the comparison with independent replicates (`t²c₀ → ½∑ᵢ(1−ηλᵢ/2)⁻²`, tide 100): stationary sampling needs an asymptotically `t`-independent number of steps for fixed precision.
**Seabed:** laplace, commit b5b7762 (tide 102 `ula-autocovariance` landed)
**Started:** 2026-09-23T06:44Z

## Candidates v1 (Claude)

Anchored quadratic model in the E2 frame `Q` (`Qᵀ H Q = diag λ`): precision `P_t = tH + g·1` with frame eigenvalues `pᵢ = tλᵢ + g`, anchored mean `m_t = P_t⁻¹ g(w₀ − c)` with `m̂ᵢ = g ŵᵢ/pᵢ` (`ŵ = affineFrame Q c w₀`); ULA step `h`, `ρᵢ = 1 − hpᵢ`, `κᵢ = 1 − hpᵢ/2`, `σᵢ² = 1/(pᵢκᵢ)`.
- **A** (Multi, fixed `t, h`; transcription of tide 102 into the anchored frame): `ulaAnchored_autoCov`: `ulaAutoCov P_t H h m_t ℓ = ½∑ᵢλᵢ²σᵢ⁴ρᵢ^{2ℓ} + ∑ᵢλᵢ²σᵢ²(gŵᵢ/pᵢ)²ρᵢ^ℓ`; `ulaAnchored_longRunVar`: `ulaLongRunVar P_t H h m_t = ∑ᵢλᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) + 2∑ᵢλᵢ²(gŵᵢ/pᵢ)²/(hpᵢ²)`.
- **B** (Limits, `h = η/t`, `0 < ηλᵢ < 2`, `g ≥ 0`): `rho_scaled_tendsto`: `1 − (η/t)(tλᵢ+g) → 1 − ηλᵢ`; `iat_quad_scaled_tendsto`: `(1+ρᵢ²)/(1−ρᵢ²) → (1+(1−ηλᵢ)²)/(1−(1−ηλᵢ)²)`; `iat_lin_scaled_tendsto`: `(1+ρᵢ)/(1−ρᵢ) → (2−ηλᵢ)/(ηλᵢ)`; `ulaScaledStep_longRunVar_main_tendsto`: `t²∑ᵢλᵢ²(1+ρᵢ²)/(4hpᵢ³κᵢ³) → ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)` (via `t²λ²/(hp³κ³) = (1/(ηλ))(tλ/(pκ))³` and tide 100's `ulaScaledStep_factor_tendsto`); `ulaScaledStep_longRunVar_mean_tendsto`: `t²·2∑ᵢλᵢ²(gŵᵢ/pᵢ)²/(hpᵢ²) = (2/η)∑ᵢ g²ŵᵢ²(tλᵢ/pᵢ)³/(λᵢpᵢ) → 0`; hence `ulaScaledStep_longRunVar_tendsto`: `t²τ²(t) → L_η := ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)`, and, using A with eventual stability (`(η/t)(tλᵢ+g) → ηλᵢ < 2`), `Tendsto (fun t => t² · ulaLongRunVar P_t H (η/t) m_t) atTop (𝓝 L_η)` (`ulaAnchored_longRunVar_tendsto`).
- **C** (Comparison): the independent-replicate variance `t²c₀(t) → ½∑ᵢ(1−ηλᵢ/2)⁻²` (main term = tide 100's `ulaScaledStep_var_main_tendsto`; mean part → 0), and the per-mode identity `[(1+(1−x)²)/(4x(1−x/2)³)] / [½(1−x/2)⁻²] = (1+(1−x)²)/(x(2−x))` (`x = ηλᵢ`): the limiting ratio of long-run to single-sample variance is the limiting quadratic integrated autocorrelation time; the effective sample size of `n` stationary steps is `n·x(2−x)/(1+(1−x)²)` per mode, `≈ nηλᵢ` for small `ηλᵢ`.
- **D** (optional): `t² · lagSumVar n → (1/n²)∑ᵢ ½(1−ηλᵢ/2)⁻²(n + 2G_n((1−ηλᵢ)²))` for fixed `n` (the scaled finite-`n` variance).

## Numerical check

`numcheck103.py` (`λ = (1, 2.5)`, `g = 0.7`, `η = 0.3`, `w = (0.8, −0.5)`): `t²τ²` = 3.2427 (t = 10) → 3.4723 (t = 10240) against `L_η = 3.47251`; the mean part 1.7e-1 → 2.2e-4 (∝ 1/t); `t²c₀` → 1.97204 against `½∑(1−ηλ/2)⁻² = 1.97204`; the IATs converge to 2.9216/1.1333 (quadratic) and 5.6667/1.6667 (linear); the ratio of the two limits per mode equals the quadratic IAT limit.
```
L = 3.472513467670806  L_c0 = 1.9720415224913497  IAT_quad lim [2.92156863 1.13333333]  IAT_lin lim [5.66666667 1.66666667]  ratio of limits per mode [2.92156863 1.13333333]
t=    10  t^2 tau^2=3.242690 (alt 3.242690)  meanpart=1.71e-01  t^2 c0=1.910472  IAT_quad=[2.71085741 1.11068651]  IAT_lin=[5.2305296  1.59403372]
t=    40  t^2 tau^2=3.414779 (alt 3.414779)  meanpart=5.19e-02  t^2 c0=1.956236  IAT_quad=[2.86606081 1.12743905]  IAT_lin=[5.55200655 1.64812976]
t=   160  t^2 tau^2=3.458098 (alt 3.458098)  meanpart=1.37e-02  t^2 c0=1.968066  IAT_quad=[2.90750332 1.13184496]  IAT_lin=[5.63762705 1.66200815]
t=   640  t^2 tau^2=3.468911 (alt 3.468911)  meanpart=3.46e-03  t^2 c0=1.971046  IAT_quad=[2.91804034 1.13296031]  IAT_lin=[5.65938297 1.66550051]
t=  2560  t^2 tau^2=3.471613 (alt 3.471613)  meanpart=8.67e-04  t^2 c0=1.971793  IAT_quad=[2.9206858  1.13324002]  IAT_lin=[5.66484425 1.66637503]
t= 10240  t^2 tau^2=3.472288 (alt 3.472288)  meanpart=2.17e-04  t^2 c0=1.971979  IAT_quad=[2.92134787 1.13331   ]  IAT_lin=[5.66621097 1.66659375]
```

## GPT-6 Astra v1

Verbatim in `gpt_autocov_scaled_v1.md` (prompt in `gpt_autocov_scaled_v1_prompt.md`). Summary:
- **A–C correct** (positive `λᵢ`, `η`, `ηλᵢ < 2`); keep `L_η = ∑(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)` in the factor-cube form (`F(x) = 2(x²−2x+2)/(x(2−x)³)`
  for asymptotics). The aggregate ratio `L_η/∑Vᵢ` is the *single-sample-variance-weighted* average of the modal IATs, not unweighted.
- **E5 wording**: "fixed absolute precision" is Monte Carlo precision for the stationary ULA expectation of the scaled statistic (the
  discretisation bias does not vanish at this scaling), in the large-`n` asymptotic-variance sense. Suggested: "for a fixed strictly stable
  scaled step `η` with `ηλᵢ < 2`, the stationary long-run variance of `tY` tends to `L_η`; the stationary asymptotic-variance step budget for
  a prescribed Monte Carlo precision is bounded and asymptotically `t`-independent; the quadratic-mode ESS fraction tends to
  `ηλᵢ(2−ηλᵢ)/(1+(1−ηλᵢ)²)`; the anchored mean contributes `O(1/t)`", strengthened by the exact rate `t·M(t) → (2g²/η)∑ŵᵢ²/λᵢ²`.
  Endpoints: `F(x) ~ 1/(2x)` as `x → 0`, `F(x) ~ 2/(2−x)³` as `x → 2` (my upper-end guess missed a factor 2); `L_η = (1/2η)∑λᵢ⁻¹ + O(1)` for
  small `η`, so `d/(2ηλ_min)` is a worst-spectrum bound, not an approximation. `ηλ = 1` gives `ρ = 0`, IAT 1 (optimal ESS fraction) but does
  **not** minimise `F` (single-mode minimiser at the root of `x³ − 2x² + 4x − 2`, `x ≈ 0.639`); `L_η` has an interior minimiser in `η`.
- **Lean**: establish eventual admissibility (`t > 0`, `pᵢ > 0`, `0 < hpᵢ < 2`, `κᵢ > 0`, via strict-limit inequalities and
  `Filter.eventually_all`) before the rational rewrites; factor-cube route for the main term; mean term via `tλᵢ/pᵢ → 1`, `1/pᵢ → 0`; state the
  `ulaLongRunVar` theorem as an unconditional-in-`t` `Tendsto` and transfer by `Tendsto.congr'` from eventual equality with the closed form
  (do not require stability for every `t`; with `g > 0` it fails near `t = 0`). Mean rate via `t·Mᵢ(t) = (2g²ŵᵢ²/(ηλᵢ²))(tλᵢ/pᵢ)⁴`.
- **Cheap additions**: (1) the mean-rate constant; (2) `IAT_quad − 1 = 2(1−x)²/(x(2−x)) ≥ 0`, hence ESS fraction `≤ 1` and `L_η ≥ ∑Vᵢ`; (3)
  fixed-lag `t²c_ℓ(t) → ½∑(1−ηλᵢ/2)⁻²(1−ηλᵢ)^{2ℓ}`; (4) D by finite summation if budget permits.
- **Vote: A+B+C + the mean-rate constant and ESS bound, fixed-lag/D if budget permits; keep the optimisation remarks as prose.**

Adopted: A–C, the mean-rate constant (`ulaScaledStep_longRunVar_mean_rate`), the ESS bound (`iat_quad_limit_sub_one`, `one_le_iat_quad_limit`,
`longRun_limit_ge_var0`), the fixed-lag limit (`ulaScaledStep_autoCov_tendsto`); D deferred. Eventual admissibility packaged as
`scaledStep_eventually`; the `ulaLongRunVar` theorem is an unconditional `Tendsto` transferred by `Tendsto.congr'` as suggested.

## Vote
- Claude: A+B+C (+ mean rate, ESS bound, fixed-lag limit)
- GPT-6 Astra: A+B+C (+ mean rate, ESS bound, fixed-lag/D if budget)

## Result

Commit `ed036a6` on `tide/autocov-scaled`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/AutocovScaled.lean` (     446 lines).
A–C as voted, plus GPT's cheap additions (mean-rate constant, ESS bound, fixed-lag limit); D deferred.
Scalar: `scaledStep_mul_tendsto`, `rho_scaled_tendsto`, `kappa_scaled_tendsto`, `scaledStep_eventually`, `one_sub_sq_pos_of_scaled`,
`iat_quad_scaled_tendsto`, `iat_lin_scaled_tendsto`, `ratio_scaled_tendsto`, `inv_scaled_tendsto`, `inv_p_tendsto`, `longRun_ratio_eq_iat`,
`iat_quad_limit_sub_one`, `one_le_iat_quad_limit`, `longRun_limit_ge_var0`.
Anchored: `transpose_mulVec_anchoredMean`, `ulaAnchored_autoCov`, `ulaAnchored_longRunVar`.
Scaled: `ulaScaledStep_longRunVar_main_tendsto`, `ulaScaledStep_longRunVar_mean_tendsto`, `ulaScaledStep_longRunVar_tendsto`,
`ulaScaledStep_var0_tendsto`, `ulaScaledStep_longRunVar_mean_rate`, `ulaScaledStep_autoCov_tendsto`.
Multi: `ulaAnchored_longRunVar_tendsto`.

Surprises: five build rounds, all bookkeeping — the substituted step `h = η/t` must be parenthesised inside generated statements
(`4 * (η / t)` vs `4 * η / t`), `field_simp` closes almost every eventual-rewrite identity on its own (trailing `ring` = "No goals"), and one
wrong factor (`1/(λp)` for `1/p`) surfaced as a `ring_nf` residue. Mathematically GPT corrected two of my prose guesses: the upper-endpoint
asymptotics of `F(x) = (1+(1−x)²)/(4x(1−x/2)³)` is `2/(2−x)³`, and `ηλ = 1` (one effective sample per step) does not minimise the long-run
variance (single-mode minimiser at `x ≈ 0.639`).
