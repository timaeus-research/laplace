# Tide: minibatch-scaled

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the β-scaled limits of tide 105's minibatch long-run variance on the anchored model (`P_t = tH + g·1`, `m_t = P_t⁻¹g(w₀−c)`, `h = η/t`): with a fixed gradient-noise covariance `C` the frame entries `Ŝᵢⱼ(t) → ηĈᵢⱼ/(λᵢ+λⱼ−ηλᵢλⱼ)` and the *unscaled* long-run variance tends to a positive constant (so the scaled statistic's is `Θ(t²)`); with linear batch growth `C = C₀/t`, `tŜᵢⱼ → (2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/(η(λᵢ+λⱼ−ηλᵢλⱼ))` and `t²τ²_{mb} → L_lin`, finite, with `L_lin(C₀ = 0) = L_η` (tide 103) and `L_η ≤ L_lin`.
**Seabed:** laplace, commit e33b32a (tide 105 `minibatch-longrun` landed)
**Started:** 2026-09-23T08:21Z

## Candidates v1 (Claude)

E2 frame `Q` (`QᵀHQ = diag λ`), `pᵢ(t) = tλᵢ + g`, `ρᵢ(t) = 1 − (η/t)pᵢ`, `m̂ᵢ(t) = gŵᵢ/pᵢ`, `Ĉ = QᵀCQ`, `0 < ηλᵢ < 2`, `w₂∞(j) = (1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))`.
- **A** (anchored transcription): `mbAnchored_longRunVar`: tide 105's `τ²_{mb}` on the anchored model with the explicit entries `Ŝᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1 − ρᵢρⱼ)` and `m̂ᵢ = gŵᵢ/pᵢ`.
- **B** (fixed `C`): `mbEntry_scaled_tendsto`: `(2(η/t)δᵢⱼ + η²Ĉᵢⱼ)/(1 − ρᵢρⱼ) → η²Ĉᵢⱼ/(1 − (1−ηλᵢ)(1−ηλⱼ)) = ηĈᵢⱼ/(λᵢ+λⱼ−ηλᵢλⱼ)`; the mean part `→ 0` (`m̂ᵢ → 0`); hence **`mbLongRunVar(P_t, H, p_t, η/t, t, C, m_t) → L_∞ := ½∑ᵢⱼλᵢλⱼ(η²Ĉᵢⱼ/(1−(1−ηλᵢ)(1−ηλⱼ)))²w₂∞(j)`** (`mbScaled_longRunVar_tendsto`) as an unconditional `Tendsto`, and **`t²·τ²_{mb}(t) → ∞`** whenever `L_∞ > 0` (`mbScaled_longRunVar_mul_sq_tendsto_atTop`; `L_∞ > 0` iff `Ĉ ≠ 0`, e.g. some `Ĉᵢᵢ > 0`).
- **C** (linear batch growth `C_t = (1/t)C₀`): `mbEntry_lin_scaled_tendsto`: `t·Ŝᵢⱼ(t) → (2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/(1 − (1−ηλᵢ)(1−ηλⱼ))`; `tm̂ᵢ → gŵᵢ/λᵢ`, `Ŝᵢⱼ → 0`; hence **`t²·mbLongRunVar(…, (1/t)C₀, …) → L_lin := ½∑ᵢⱼλᵢλⱼ((2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/(1−(1−ηλᵢ)(1−ηλⱼ)))²w₂∞(j)`** (`mbScaled_lin_longRunVar_tendsto`).
- **D** (comparison): `L_lin(C₀ = 0) = L_η = ∑ᵢ(1+(1−ηλᵢ)²)/(4ηλᵢ(1−ηλᵢ/2)³)` (`Llin_zero_eq`), and `L_η ≤ L_lin` for `Ĉ₀ ⪰ 0` (`Leta_le_Llin`; termwise, diagonal via `Ĉ₀ᵢᵢ ≥ 0`).

## Numerical check

`numcheck106.py` (3D random frame, `λ = (1, 2.5, 0.7)`, `g = 0.7`, `η = 0.3`, random PSD `C₀` of scale 0.05): fixed `C`: `τ²_{mb}(t)` = 0.0939 (t = 10) → 0.007755 (t = 10240) against `L_∞ = 0.007724`, mean part `∝ t⁻³`, `t²τ²` → 8e5; `C₀/t`: `t²τ²_{mb}` = 6.113 → 6.5139 against `L_lin = 6.5142`; `L_lin(C₀ = 0) = L_η = 6.1694`.
```
Linf 0.007724189105171162  Llin 6.514174264649015  L_eta (ULA) 6.169410555640505  Llin with C0=0 6.169410555640505
t=    10 fixed C: tau2=0.093896 (mean part 1.02e-02) t^2 tau2=9.390e+00 | C0/t: t^2 tau2=6.113292 (mean part 7.14e-01)
t=    40 fixed C: tau2=0.019222 (mean part 4.13e-04) t^2 tau2=3.075e+01 | C0/t: t^2 tau2=6.430835 (mean part 2.31e-01)
t=   160 fixed C: tau2=0.009927 (mean part 2.08e-05) t^2 tau2=2.541e+02 | C0/t: t^2 tau2=6.494842 (mean part 6.17e-02)
t=   640 fixed C: tau2=0.008232 (mean part 1.21e-06) t^2 tau2=3.372e+03 | C0/t: t^2 tau2=6.509444 (mean part 1.57e-02)
t=  2560 fixed C: tau2=0.007849 (mean part 7.43e-08) t^2 tau2=5.144e+04 | C0/t: t^2 tau2=6.512998 (mean part 3.94e-03)
t= 10240 fixed C: tau2=0.007755 (mean part 4.62e-09) t^2 tau2=8.132e+05 | C0/t: t^2 tau2=6.513881 (mean part 9.86e-04)
```

## GPT-6 Astra v1

Verbatim in `gpt_minibatch_scaled_v1.md` (prompt in `gpt_minibatch_scaled_v1_prompt.md`). Summary:
- **A–D correct** (`η > 0`, `λᵢ > 0`, `0 < ηλᵢ < 2`, fixed frame; PSD for the comparison). With `rᵢ = 1 − ηλᵢ`, `dᵢⱼ = 1 − rᵢrⱼ = η(λᵢ+λⱼ−ηλᵢλⱼ) > 0`;
  `Ŝᵢⱼ(t) → η²Ĉᵢⱼ/dᵢⱼ`, the unscaled mean part vanishes (its `t²`-scaled version need not, but does not affect the leading `L_∞t²`), so
  `τ²_{mb}(t) → L_∞` and **`L_∞ > 0 ⟺ Ĉ ≠ 0`** (every coefficient of `Ĉᵢⱼ²` is strictly positive; no PSD needed). `C`: `tŜᵢⱼ → (2ηδᵢⱼ + η²Ĉ₀ᵢⱼ)/dᵢⱼ`,
  `tm̂ᵢ → gŵᵢ/λᵢ`, `Ŝ → 0`, so the scaled mean summand `(tm̂ᵢ)(tm̂ⱼ)Ŝᵢⱼw₁ → 0` and `L_lin` is exactly right. `D`: at `C₀ = 0`, `Aᵢᵢ = 1/(λᵢ(1−ηλᵢ/2))`
  gives `L_η`; for PSD `Ĉ₀ ≠ 0`, `L_lin > L_η` strictly (a nonzero PSD matrix has a positive diagonal entry).
- **Wording**: "at fixed stable `η`, a nonzero `t`-independent gradient-noise covariance gives `t²τ²_{mb}(t) ~ L_∞t²`, so the stationary chain
  average needs `n = Θ(t²)` for fixed precision; with `C_t = C₀/t` the coefficient converges to `L_lin(C₀) ≥ L_η`, with equality iff `C₀ = 0`."
  Qualifications: long-run variance is a large-`n` coefficient (no simultaneous `(t, n(t))` theorem without finite-`n` remainder control);
  "linear batch growth" presumes inverse scaling with batch size; distinguish chain iterations from gradient evaluations (batch `Θ(t)` ×
  iterations). `L_∞` is the long-run variance of the limiting noise-driven chain `S^∞ = RS^∞R + η²Ĉ` — the stationary noise floor left when the
  thermal noise vanishes; `L_∞ = (η/2)∑ᵢⱼλᵢλⱼĈᵢⱼ²wⱼ(η)/Dᵢⱼ²` is `η` times an `η`-dependent Lyapunov-type functional.
- **Lean**: normalise by `t` before applying limit lemmas (`u = 1/t`); reusable denominator positivity; separate entry limits from finite-sum
  assembly; scaled identities `t²S² = (tS)²`, `t²m̂ᵢm̂ⱼS = (tm̂ᵢ)(tm̂ⱼ)S` by `ring`; transfer to the actual long-run variance last by `Tendsto.congr'`
  (for `C₀/t`, PSD needs `t > 0`, only eventual); divergence via an eventual lower bound if the product lemma is awkward.
- **Cheap additions**: (1) `L_∞ > 0 ⟺ Ĉ ≠ 0`; (2) strictness in D; (3) a general lemma organised around `tĈ_t → B` (covers linear and all
  superlinear scalings with `tĈ_t → 0`, e.g. `C₀/t²` recovering `L_η`) instead of power-law cases.
- **Vote: land A–D plus `L_∞ > 0 ⟺ C ≠ 0`; organise C around `tC_t → B`, take `C₀/t²` as the cheap corollary, defer real-power scaling.**

Adopted: A–D and `Linf_pos_of_ne` (the direction needed for the divergence theorem: one nonzero frame entry gives `L_∞ > 0`). Deferred: the
converse, strictness in D, the general `tĈ_t → B` organisation and the `C₀/t²` corollary, the `(η/2)`-factorised form.

## Vote
- Claude: A–D (+ `L_∞ > 0` from a nonzero entry)
- GPT-6 Astra: A–D + `L_∞ > 0 ⟺ C ≠ 0` (+ general `tC_t → B` organisation)
