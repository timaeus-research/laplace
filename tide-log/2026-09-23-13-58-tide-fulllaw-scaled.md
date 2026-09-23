# Tide: fulllaw-scaled

**Direction (user):** auto mode — E8 at the anchored scaling: the first-order Hessian-fluctuation correction to the LLC grows linearly in `t` at fixed relative step, with an explicit slope, alongside the constant-noise inflation slope.
**Seabed:** laplace, commit b6d1f1c (tide 115 `FullLawResolvent` (`fullLaw_llc_ge'`), tide 106 `MinibatchScaled` (`mbEntry_scaled_tendsto`), tide 101 `MinibatchBudget` (`minibatchCov_frame_apply`))
**Started:** 2026-09-23-13-58 UTC

## Candidates v1 (Claude)

Setting: `h = η/t`, `pⱼ = tλⱼ + g`, `ρⱼ = 1 − hpⱼ → αⱼ = 1 − ηλⱼ`; fixed gradient-noise covariance `C` (frame `Ĉ = QᵀCQ`), fixed Hessian deviations `Dᵢ`,
fixed `c` (the note's `c = h²t²(1−m/n)/(m(n−1)) = η²(1−m/n)/(m(n−1))` is constant at this scaling). Tide 115: `LLC_full ≥ LLC^{mb} + (t/2)c∑ⱼλⱼ(B̂(Σ^{mb}))ⱼⱼ/(1−ρⱼ²)`.

- **A** (`mbCov_frame_tendsto`, `mbCov_tendsto`): `(QᵀΣ^{mb}(t)Q)ₖₗ = (2(η/t)δₖₗ + η²Ĉₖₗ)/(1−ρₖρₗ) → Ŝ∞ₖₗ := η²Ĉₖₗ/(1−αₖαₗ)` (tide 106's entry limit), hence
  `Σ^{mb}(t) → Σ∞ := QŜ∞Qᵀ` as matrices: the minibatch stationary covariance has an `O(1)` limit at fixed relative step (the noise term
  dominates the `O(1/t)` ULA part).
- **B** (`firstOrder_slope_tendsto`): **`(1/t)·(t/2)c∑ⱼλⱼ(B̂(Σ^{mb}(t)))ⱼⱼ/(1−ρⱼ(t)²) → σ₁ := ½c∑ⱼλⱼ(QᵀB(Σ∞)Q)ⱼⱼ/(ηλⱼ(2−ηλⱼ))`** by continuity of
  `Σ ↦ (QᵀB(Σ)Q)ⱼⱼ`: the first-order Hessian-fluctuation correction grows linearly in `t`.
- **C** (`mb_slope_tendsto`): `(1/t)(LLC^{mb}(t) − LLC^{ULA}(t)) → σ_mb := (η/4)∑ⱼĈⱼⱼ/(1−ηλⱼ/2)` (the constant-noise inflation slope of Summary 2).
- **D** (`fullLaw_lower_slope_tendsto`): `(1/t)(LLC^{mb} + first-order term − LLC^{ULA}) → σ_mb + σ₁`: asymptotically the full-law LLC mean exceeds the
  exact-gradient value by at least `t(σ_mb + σ₁)`.

## Numerical check

`numcheck116.py` (3D random frame, 4 per-sample Hessians, `m = 2`, `η = 0.3`, `g = 0.7`):
```
predicted slopes: first-order fluctuation 0.015943   constant-noise inflation 0.276365   ratio 0.0577
  t=   1e+01  corr1/t = 0.023168   (LLC_mb − LLC_ula)/t = 0.265425
  t=   1e+02  corr1/t = 0.016771   (LLC_mb − LLC_ula)/t = 0.275186
  t=   1e+03  corr1/t = 0.016027   (LLC_mb − LLC_ula)/t = 0.276246
  t=   1e+04  corr1/t = 0.015951   (LLC_mb − LLC_ula)/t = 0.276353
  t=   1e+05  corr1/t = 0.015944   (LLC_mb − LLC_ula)/t = 0.276364
```

## GPT-6 Astra v1

Full response in `gpt_fulllaw-scaled_v1.md`. Summary: **approve A–D** under `λⱼ > 0`, `0 < ηλⱼ < 2`, fixed `g, C, Dᵢ`, `C ⪰ 0`, `c ≥ 0`. Two
qualifications: (i) `c` is `t`-independent only because the note's coefficient has the form `γh²t²` (display it); (ii) the limit of `B̂(Σ^{mb})ⱼⱼ` is
finite but can vanish: `B(Σ∞) = ∑ᵢ(DᵢΣ∞^{1/2})(DᵢΣ∞^{1/2})ᵀ`, so `σ₁ > 0` iff some `DᵢΣ∞^{1/2} ≠ 0`; the first-order term is `O(t)` always and `Θ(t)`
when `σ₁ > 0`. Reconciliation with tides 107/114: `1 − ρⱼ² = hpⱼ(2−hpⱼ)` is `Θ(h)` at fixed `pⱼ`, `h → 0`, but tends to `sⱼ = ηλⱼ(2−ηλⱼ) > 0` along
`pⱼ = tλⱼ + g`, `h = η/t`; so the additive resolvent is `O(1)` at the anchored scaling. This does not establish stability of the full law along
the scaling (limiting operator `T∞(X) = A∞XA∞ᵀ + cB(X)`, needs `spr(T∞) < 1` separately). Diagnostic: `R₁ = σ₁/σ_mb` is a noise-weighted average of
modewise feedback strengths `qⱼ = cvⱼ/(ηλⱼ(2−ηλⱼ))` (`vⱼ = ∑ᵢd̂ᵢⱼ²`) with weights `wⱼ = ηĈⱼⱼ/(2(2−ηλⱼ))` when the `Dᵢ` share the eigenframe; then
`σ₁ = (c/2)∑ⱼvⱼĈⱼⱼ/(λⱼ(2−ηλⱼ)²)` and the full slope in that setting is `∑ⱼwⱼ/(1−qⱼ)`, which shows why the first-order diagnostic understates the
effect near `qⱼ = 1` (higher-order Hessian-fluctuation terms are also `Θ(t)` at fixed `c`). Wording: say "the first-order Hessian-fluctuation term
has slope `σ₁`", and `liminf (LLC_full − LLC^{ULA})/t ≥ σ_mb + σ₁` whenever the full law exists for large `t`; keep the note's `ht²tr(C_g)/(2d)` only
with its normalisation assumptions (fixed relative step does not make `1 − ηλⱼ/2 → 1`).

## Vote
- Claude: A + B + C + D
- GPT-6 Astra: "yes to A–D and to adding the diagnostic; revise 'the Hessian-fluctuation correction has slope σ₁' to 'the first-order Hessian-fluctuation term has slope σ₁'"
