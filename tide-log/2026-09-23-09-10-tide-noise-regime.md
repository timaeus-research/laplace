# Tide: noise-regime

**Direction (user):** auto mode — continue the Sanity-on-Sampling E8+E5 story: the general scaled-noise regime `t·Ĉ_t → B` for the minibatch long-run variance at the anchored scaling, with the batch-size corollaries and strictness.
**Seabed:** laplace, commit 036a2b8 (tides 105–106 `MinibatchLongRun`, `MinibatchScaled`; 108 `BurnInLog`)
**Started:** 2026-09-23-09-10 UTC

## Candidates v1 (Claude)

Setting (tide 106, `mbAnchored_longRunVar`): on the anchored model at step `h = η/t` with noise covariance `C`, the long-run variance of the sampled
energy is `τ²_mb = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²(1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(1+ρⱼ)/(1−ρⱼ)`, `Ŝᵢⱼ = (2hδᵢⱼ + h²t²Ĉᵢⱼ)/(1−ρᵢρⱼ)`, `Ĉ = QᵀCQ`. Tide 106 treated
fixed `C` (`t²τ² → ∞`) and `C = C₀/t` (`t²τ² → L_lin`). The general statement is organised around the scaled frame noise `tĈ_t`.

Write `L(B̂) := ½∑ᵢⱼλᵢλⱼ((2ηδᵢⱼ + η²B̂ᵢⱼ)/(1−(1−ηλᵢ)(1−ηλⱼ)))²(1+(1−ηλⱼ)²)/(ηλⱼ(2−ηλⱼ))` (`scaledNoiseLimit`), so `L(Ĉ₀) = L_lin` and `L(0) = L_η`.

- **A** (`mbEntry_general_scaled_tendsto`): if `t·c(t) → b` then `t·(2(η/t)δ + (η/t)²t²c(t))/(1−ρᵢρⱼ) → (2ηδ + η²b)/(1−(1−ηλᵢ)(1−ηλⱼ))`, and the
  unscaled entry → 0.
- **B** (`mbGeneral_longRunVar_tendsto`): for `C : ℝ → Matrix` eventually PSD with `t·(QᵀC_tQ)ᵢⱼ → B̂ᵢⱼ` for all `i, j`, `t²τ²_mb(t) → L(B̂)`
  (the mean part is `O(1/t)`).
- **C** corollaries: (C1) `C_t = C₀/t²`, or any `C_t` with `tĈ_t → 0` (super-linear batch growth): `t²τ²_mb → L_η`, the exact-gradient value; (C2)
  batch-size form: `C_t = C_g/n_t` with `n_t/t → ν > 0` gives `t²τ²_mb → L(Ĉ_g/ν)` — the inflation is set by the ratio batch/temperature.
- **D** strictness (`Leta_lt_scaledNoiseLimit`): for `B̂` with nonnegative diagonal (e.g. PSD), `L_η < L(B̂) ⟺ B̂ ≠ 0`; in particular `L_η < L_lin`
  for PSD `C₀ ≠ 0`.
- **E** monotonicity (`scaledNoiseLimit_mono`): if `0 ≤ B̂₁ᵢᵢ`, `0 ≤ B̂₂ᵢᵢ` and `|B̂₁ᵢⱼ| ≤ |B̂₂ᵢⱼ|` entrywise then `L(B̂₁) ≤ L(B̂₂)`; hence in C2 the
  limit decreases as `ν` grows.

Regime summary: sub-linear batch growth → `t²τ² → ∞` (tide 106), linear → finite inflation `L(B̂) > L_η`, super-linear → `L_η`.

## Numerical check

`numcheck109.py` (`λ = (1, 2.5, 0.7)`, `η = 0.3`, `g = 0.7`, random orthogonal `Q`, random PSD `B, D, C_g`):
```
L_eta = 6.169410555640505  LB(0) = 6.169410555640506
regime t*C_t -> B  (C_t = B/t + D/t^1.5):  target LB = 24.141801160775472
  t=   1e+02  t^2 tau2 = 25.245936
  t=   1e+03  t^2 tau2 = 24.579490
  t=   1e+04  t^2 tau2 = 24.288668
  t=   1e+05  t^2 tau2 = 24.189075
  t=   1e+06  t^2 tau2 = 24.156833
regime C_t = C0/t^2 (superlinear batch): target L_eta = 6.169410555640505
  t=   1e+02  t^2 tau2 = 6.211662
  t=   1e+03  t^2 tau2 = 6.173766
  t=   1e+04  t^2 tau2 = 6.169847
  t=   1e+05  t^2 tau2 = 6.169454
  t=   1e+06  t^2 tau2 = 6.169415
batch n_t = nu t + 5 sqrt t, C_t = Cg/n_t:  target LB(Chat_g/nu) = 8.31159948764244
  t=   1e+02  t^2 tau2 = 7.899060
  t=   1e+03  t^2 tau2 = 8.186806
  t=   1e+04  t^2 tau2 = 8.272583
  t=   1e+05  t^2 tau2 = 8.299302
  t=   1e+06  t^2 tau2 = 8.307715
strictness: LB(B) - L_eta = 17.97239060513497  (>0);  LB(Cg/1) - LB(Cg/3) = 5.41076171212719  (>0, monotone in 1/nu)
```

## GPT-6 Astra v1

Full response in `gpt_noise-regime_v1.md` (prompt in `gpt_noise-regime_v1_prompt.md`). Summary:

- **A–E correct.** Eventually-PSD is the right probabilistic hypothesis but the limit theorem is purely algebraic; `B̂` inherits PSD-ness
  (entrywise limits of PSD matrices), so the nonnegative-diagonal hypothesis is automatic in applications. The strictness identity
  `L(B) − L(0) = 4η³∑ᵢwᵢᵢBᵢᵢ + η⁴∑ᵢⱼwᵢⱼBᵢⱼ²` (positive weights `wᵢⱼ`) shows there is no off-diagonal cancellation. The entrywise
  absolute-value monotonicity is valid; the stronger PSD-order monotonicity `0 ⪯ B₁ ⪯ B₂ ⟹ L(B₁) ≤ L(B₂)` also holds (Gram kernel
  `(1+rᵢrⱼ)/(1−rᵢrⱼ)` + Schur product) but is a separate tide.
- **C2 needs `n_t > 0` eventually** (integer-valued schedules fine).
- **Cheap additions recommended**: strict anti-monotonicity in `ν` for `C_g ≠ 0`; the sub-linear divergence corollary
  (`n_t/t → 0 ⟹ t²τ²_mb → ∞`) if the trichotomy is claimed (the fixed-`C` theorem alone covers only constant batch); the mean coefficient
  `t³M_t → A_mean = ∑ᵢⱼλᵢλⱼ(gŵᵢ/λᵢ)(gŵⱼ/λⱼ)((2ηδᵢⱼ+η²Bᵢⱼ)/dᵢⱼ)((1+rⱼ)/(1−rⱼ))` (needs no rate). Formulate divergence as norm or
  specified-entry divergence, not "`tĈ_t → ∞` entrywise" (PSD matrices can have permanent zero entries).
- **Wording**: "for fixed model, fixed `C_g` and fixed `η = ht`, the limiting scaled stationary LRV is determined by `n_t/t`"; caveats:
  `t` is inverse temperature, the fixed quantity is `η` not `h`, stationary infinite-horizon LRV, constant-in-state covariance with
  Gaussian innovations (constant covariance alone does not give Gaussian stationarity), the batch model `C_g/n_t` must apply.

## Candidates v2 (Claude, adopting the additions)

- **F** (`mbBatch_longRunVar_tendsto_atTop`): `C_t = C_g/n_t`, `n_t → ∞`, `n_t/t → 0`, some frame diagonal entry `(QᵀC_gQ)ᵢᵢ > 0` ⟹
  `t²τ²_mb → ∞` (the `(i,i)` quadratic term dominates; the mean part → 0 since `n_t → ∞`). Divergence is stated through one positive diagonal
  entry, as GPT advised.
- **G** (`mbBatch_longRunVar_tendsto_Leta`): `n_t/t → ∞` ⟹ `t²τ²_mb → L_η`. With C2 and F this is the batch trichotomy.
- **H** (`scaledNoiseLimit_lt`, `scaledNoiseLimit_batch_anti_strict`): strict monotonicity; `0 < ν₁ < ν₂`, `C_g ≠ 0` ⟹ `L(Ĉ_g/ν₂) < L(Ĉ_g/ν₁)`.
- **I** (`mbGeneral_meanPart_mul_tendsto`): `t·MEAN_t → A_mean` under B's hypotheses.

## Numerical check v2
```
--- v2 additions ---
sublinear n_t = sqrt(t) (n_t -> inf, n_t/t -> 0): t^2 tau2 should diverge
  t=   1e+02  t^2 tau2 = 2.3065e+02
  t=   1e+03  t^2 tau2 = 1.8786e+03
  t=   1e+04  t^2 tau2 = 1.7486e+04
  t=   1e+05  t^2 tau2 = 1.7082e+05
  t=   1e+06  t^2 tau2 = 1.6954e+06
mean coefficient: t^3 * meanpart(C_t = B/t + D/t^1.5) -> A_mean = 8.556086491417904
  t=   1e+02  t^3 mean = 8.228238
  t=   1e+03  t^3 mean = 8.524320
  t=   1e+04  t^3 mean = 8.553461
  t=   1e+05  t^3 mean = 8.556000
  t=   1e+06  t^3 mean = 8.556134
```

## Vote
- Claude: A + B + C1 + C2 + D + E, plus F–I
- GPT-6 Astra: "ship A–D and the stated E … also prove a batch-specific sublinear-divergence corollary … the mean coefficient is a particularly cheap optional addition"

## Result

Commit `71a2527` on `tide/noise-regime`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/NoiseRegime.lean` (     606 lines).
A–E as voted plus the GPT-suggested additions F–I (sub-linear divergence, super-linear corollary, strict monotonicity, mean coefficient).
Lemmas: `scaledNoiseLimit` (def), `iat_weight_pos`, `mbEntry_general_scaled_tendsto`, `mbEntry_general_tendsto_zero`, `mbEntry_batch_tendsto_zero`,
`mbAnchored_sq_longRunVar_eq`, `mbMeanPart_tendsto_zero`, `mbGeneral_longRunVar_tendsto`, `mbGeneral_meanPart_mul_tendsto`, `scaledNoiseLimit_zero`,
`Llin_eq_scaledNoiseLimit`, `mbGeneral_longRunVar_tendsto_Leta`, `mbScaled_quad_longRunVar_tendsto`, `mbBatch_longRunVar_tendsto`,
`mbBatch_longRunVar_tendsto_Leta`, `mbBatch_longRunVar_tendsto_atTop`, `entry_sq_mono`, `entry_sq_lt`, `scaledNoiseLimit_mono`, `scaledNoiseLimit_lt`,
`Leta_le_scaledNoiseLimit`, `Leta_lt_scaledNoiseLimit_iff`, `frame_diag_nonneg`, `conj_eq_zero_iff`, `exists_conj_ne_zero`, `Leta_lt_Llin`,
`scaledNoiseLimit_batch_anti`, `scaledNoiseLimit_batch_anti_strict`.

Surprises: the extended file compiled on its first build after the v1 core had needed one repair round (a section variable `Q` out of scope in a
statement that does not mention it, `id`/`Pi.div` residues after `Tendsto.div_atTop`/`Tendsto.div`, and the deprecated `push_neg`). Splitting
`t²τ²_mb` into the `t`-scaled quadratic part and the mean part once (`mbAnchored_sq_longRunVar_eq`) made B, the divergence and the mean coefficient
one-line consumers of the same identity. The divergence needed `n_t → ∞` so that the mean part vanishes; GPT's remark that a nonzero PSD matrix
must be detected through a positive diagonal entry (not entrywise divergence) fixed the hypothesis.
