# Tide: anchored-covariance-gap

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: E3's anchored Gaussian covariance of the quadratic energy with quadratic-plus-linear probes (the susceptibility side), exact via the tilted-Gaussian Wick machinery of tide 96, its eigen form and `1/t` expansion, and the susceptibility gap against the landed E2 second-order `covK` theorem: a leading-order gap for linear probe parts (the cubic mean shift) and a purely anharmonic "gap matrix" `Γ` at order `1/t`.
**Seabed:** laplace, commit eab0ed3 (tide 96 `anchored-variance-gap` landed)
**Started:** 2026-09-23T03:34Z

## Candidates v1 (Claude)

`Σ = P⁻¹`, `m = P⁻¹v`, `H`, `B` symmetric, `pᵢ = tλᵢ + g`, `aᵢ = (Uᵀv)ᵢ`, `B̃ = UᵀBU`, `b̃ = Uᵀb`.
- **A** (Sampler): `tiltedCov_quadForm`: `Cov_{P,v}(uᵀHu, uᵀBu) = 2tr(HΣBΣ) + 4(Hm)ᵀΣ(Bm)` (mixed Wick integral
  `∫(uᵀHu)(uᵀBu) gw = Z(tr(HΣ)tr(BΣ) + 2tr(HΣBΣ))`); `tiltedCov_quadForm_linear`: `Cov_{P,v}(uᵀHu, b·u) = 2bᵀΣ(Hm)`.
- **B** (Sampler, eigen): `t²Cov_{tH+gI,v}(½uᵀHu, ½uᵀBu + b·u) = ½∑ᵢB̃ᵢᵢ(tλᵢ/pᵢ)²/λᵢ + t²∑ᵢⱼλᵢaᵢB̃ᵢⱼaⱼ/(pᵢ²pⱼ) + t²∑ᵢb̃ᵢλᵢaᵢ/pᵢ²`.
- **C** (Multi): `B = ∑ᵢ(B̃ᵢᵢ/(2λᵢ) + b̃ᵢaᵢ/λᵢ) + [−g∑B̃ᵢᵢ/λᵢ² + ∑ᵢⱼB̃ᵢⱼaᵢaⱼ/(λᵢλⱼ) − 2g∑b̃ᵢaᵢ/λᵢ²]/t + O(t⁻²)`, explicit constant.
- **D** (Multi): `t²Cov_loc(L∘A, ψ) − t²Cov_anch = −∑ᵢb̃ᵢαᵢ/(2λᵢ²) + Γ_B/t + O(t⁻²)`,
  `Γ_B = ∑ᵢB̃ᵢᵢΓᵢᵢ + ∑_{i≠j}B̃ᵢⱼ(cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)) + 2∑ᵢb̃ᵢ(m₂ᵢ + gaᵢ/λᵢ²)`, `Γᵢᵢ = 5αᵢ²/(4λᵢ⁴) − 2aᵢαᵢ/λᵢ³ − γᵢ/(2λᵢ³)`,
  from `localisedRotatedAnharmonic_covK_order2_rate` and C.

## Numerical check

`numcheck_anchored_covariance_gap.py` (λ = (1.3, 0.9), α = (0.7, −0.4), γ = (1.1, 0.8), g = 0.8, u₀ = (0.55, −0.35), B̃ = [[0.9, 0.4],[0.4, 1.6]], b̃ = (0.3, −0.5)):
formula B equals direct Gaussian integration to 1e-10 (t = 50); leading gap −0.185587 = `−∑b̃ᵢαᵢ/(2λᵢ²)` exactly; `t·(gap − leading)`: −0.28373 (t = 40) → −0.31099 (t = 640) vs `Γ_B = −0.31263`; `t²`-remainder 1.16 → 1.05, converging; the 1D closed forms `m₂ = 0.10310, −0.31297` and `c₂′ = −0.67509, −1.44200` reproduced numerically (0.10251, −0.31099; −0.67408, −1.43872 at t = 640).

## Questions for GPT-6 Astra (prompt in `gpt_anchored_covariance_gap_prompt_v1.md`)

Correctness of A–D (mixed Wick, cross term, linear covariance, non-diagonal `B̃`, gap coefficients); relation of `Γ_H` to `2C₁′`; direct mixed Wick vs polarisation; frame identification by prose (as tides 95–96); wording; vote.

## GPT-6 Astra v1 (summary; verbatim in `gpt_anchored_covariance_gap_v1.md`)

- A–D correct (P ≻ 0 symmetric, H, B symmetric, λᵢ > 0). Mixed Wick `∫(uᵀHu)(uᵀBu) gw = Z(tr(HΣ)tr(BΣ) + 2tr(HΣBΣ))`; cross term `4(Hm)ᵀΣ(Bm)` automatically symmetric in H ↔ B (Σ symmetric); linear `2bᵀΣ(Hm)`; B needs no diagonal assumption on `B̃`; all gap coefficients confirmed (leading `−∑b̃ᵢαᵢ/(2λᵢ²)`, `Γᵢᵢ = 5α²/(4λ⁴) − 2aα/λ³ − γ/(2λ³)`, off-diagonal `cᵢcⱼ − aᵢaⱼ/(λᵢλⱼ)` over *ordered* pairs, linear `2(m₂ + ga/λ²)`); remainder constant `K_loc + K_anch` with `K_anch = (3g²/2)∑|B̃ᵢᵢ|/λᵢ³ + 3g²∑|b̃ᵢaᵢ|/λᵢ³ + g∑ᵢⱼ|B̃ᵢⱼaᵢaⱼ|(2/λᵢ + 1/λⱼ)/(λᵢλⱼ)` (adopted).
- `Γ_H ≠ 2C₁′` is necessary: `Var_loc(L) = Cov(L, L₂) + Cov(L, L₃) + Cov(L, L₄)`; the identity `2C₁′ − Γ_H = ∑(−5αᵢ²/(6λᵢ³) + aᵢαᵢ/λᵢ² + γᵢ/(4λᵢ²))` is the cubic+quartic probe contribution (recorded, not formalised this tide).
- Lean route: prefers polarisation for `tiltedCov_quadForm`; we kept the direct mixed Wick proof (a copy of tide 96's, which already compiled) and derived `tiltedCov_quadForm` from the probe covariance with `b = 0`. Odd moments by reflection (existing lemma). Adopted GPT's bridge: the eigenframe formula is proved for an arbitrary orthogonal `U` with `UᵀU = 1`, `UᵀHU = diag(λ)` (`anchoredGaussianCov_eq`), instantiated with `Q` in the Multi theorem, so the gap is stated against the actual tilted-Gaussian covariance, not a frame formula.
- Wording qualifications: "quadratic" = purely quadratic about the expansion centre (`b = 0`); "purely anharmonic" = vanishes in the harmonic limit, but `Γ` depends on the anchor `a = g u₀`; "no Gaussian reproduces the leading linear gap" too strong — the *Hessian-anchored* Gaussian does not (a Gaussian with an anharmonically corrected mean would); leading gap can vanish by cancellation; `Γ` need not be PSD.

## Vote
- Claude: A–D (`tiltedCov_quadForm_quadProbe`, `tiltedCov_quadForm`, `anchoredGaussianCov_eq` in an arbitrary frame, `anchoredGaussianCov_rate2`, `localisedCov_anchoredGap`), cubic/quartic identity recorded only
- GPT-6 Astra: land A–D; polarisation (we used direct Wick), arbitrary-eigenframe bridge (adopted), record the cubic/quartic identity, qualify the E3 claim
