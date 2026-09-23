# Tide: minibatch-fluctuation

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the deferred E8 fluctuation piece — positive definiteness of the Lyapunov (minibatch SGLD) stationary covariance via its geometric-series representation, the variance of the energy `½uᵀHu` under the minibatch stationary law with the full (off-diagonal) frame entries `Σ̂ᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1−ρᵢρⱼ)`, and its excess over the ULA variance (first order: `(ht²/2)∑λᵢ²σᵢ⁴Ĉᵢᵢ`; `Σ^{mb} − Σ^{ULA} = lyapunovVia(h²t²C) ⪰ 0`).
**Seabed:** laplace, commit 01e3ab3 (tide 103 `autocov-scaled` landed)
**Started:** 2026-09-23T07:33Z

## Candidates v1 (Claude)

Frame `U` (`UᵀU = 1`) diagonalising `P` (`p`) and `H` (`λ`); `ρᵢ = 1 − hpᵢ`, `|ρᵢ| < 1`; `N = minibatchNoise h t C = 2h·1 + h²t²C`, `N̂ = UᵀNU`, `Ĉ = UᵀCU`; `Σ = lyapunovVia U ρ N = U·diagLyapunov ρ N̂·Uᵀ`, `Σ̂ᵢⱼ = N̂ᵢⱼ/(1−ρᵢρⱼ) = (2h[i=j] + h²t²Ĉᵢⱼ)/(1−ρᵢρⱼ)` (tide 101); `σᵢ² = 1/(pᵢκᵢ) = 2h/(1−ρᵢ²)`.
- **A** (Sampler, Lyapunov positivity): `diagLyapunov_quadForm_eq_tsum`: `x ⬝ᵥ diagLyapunov a N x = ∑'_{r} (aʳ∘x) ⬝ᵥ N (aʳ∘x)` (`(aʳ∘x)ᵢ = aᵢʳxᵢ`; geometric series `1/(1−aᵢaⱼ) = ∑'_r (aᵢaⱼ)ʳ` and two finite-sum swaps); hence `diagLyapunov_posSemidef` (`N ⪰ 0 ⇒ diagLyapunov a N ⪰ 0`) and `diagLyapunov_posDef` (`N ≻ 0 ⇒ ≻ 0`, the `r = 0` term dominates: `xᵀ diagLyap x ≥ xᵀNx > 0`), transported: `lyapunovVia_posDef`; `minibatchNoise_posDef` (`h > 0`, `C ⪰ 0`) ⇒ `minibatchCov_posDef_frame`: `Σ ≻ 0`.
- **B** (Sampler, the minibatch fluctuation): with the stationary law `N(m, Σ)` as the tilted Gaussian `(Σ⁻¹, Σ⁻¹m)`,
  `minibatchVar_frame`: **`Var(½uᵀHu) = ½∑ᵢ∑ⱼ λᵢλⱼΣ̂ᵢⱼ² + ∑ᵢ∑ⱼ λᵢλⱼm̂ᵢm̂ⱼΣ̂ᵢⱼ`** (tide 96's `tiltedVar_quadForm` + frame lemmas for a non-diagonal middle factor: `∑ₐ∑_c (UM₁Uᵀ)ₐ_c(UM₂Uᵀ)_cₐ = ∑ᵢⱼ(M₁)ᵢⱼ(M₂)ⱼᵢ`, `x ⬝ᵥ (UMUᵀ)y = (Uᵀx) ⬝ᵥ M(Uᵀy)`). The off-diagonal noise entries enter the variance (they do not enter the mean, tide 101).
- **C** (excess over ULA): `Σ̂ᵢⱼ = σᵢ²[i=j] + Eᵢⱼ`, `Eᵢⱼ = h²t²Ĉᵢⱼ/(1−ρᵢρⱼ)` (`minibatchCov_frame_split`); `minibatchVar_sub_ulaVar`: **`Var^{mb} − Var^{ULA} = ½∑ᵢⱼλᵢλⱼ(2σᵢ²[i=j]Eᵢⱼ + Eᵢⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼEᵢⱼ`**, whose first-order diagonal part is `∑ᵢλᵢ²σᵢ²Eᵢᵢ = (ht²/2)∑ᵢλᵢ²σᵢ⁴Ĉᵢᵢ` (`minibatch_var_firstOrder`): to first order in `C` the variance inflates by the same per-mode factor `1 + ht²Ĉᵢᵢ/2` as the mean, the off-diagonal `Ĉᵢⱼ` entering at `O(C²)`; `lyapunovVia_add` (linearity in `N`), `lyapunovVia_ulaNoise_eq_ulaCov` (`lyapunovVia U ρ (2h·1) = ulaCov P h`), hence **`Σ^{mb} − Σ^{ULA} = lyapunovVia U ρ (h²t²C) ⪰ 0`** (`minibatchCov_sub_ulaCov_posSemidef`).
- **D** (optional): `Var^{mb} ≥ Var^{ULA}` (needs `tr(BE) ≥ 0` for PSD `B, E`, i.e. monotonicity of `tr((HΣ)²)` and `mᵀHΣHm` in `Σ`).

## Numerical check

`numcheck104.py` (3D, random frame, `t = 20`, `g = 0.7`, `h = 0.3/t`, random PSD `C` of scale 0.05): the Lyapunov fixed point matches the frame formula; the series representation of `xᵀΣ̂x` and its first term bound; `Var` exact = frame formula = Monte Carlo; the split `Σ̂ = diag(σ²) + E`, the excess formula, the first-order diagonal term, and `Σ^{mb} − Σ^{ULA} = lyapunovVia(h²t²C)` with positive smallest eigenvalue.
```
lyapunov fixed point err 1.3877787807814457e-17
x^T S x 0.07725271336838543 series 0.07725271336838539 first term 0.05705989691592039 eigmin Sigma 0.03574500670517597
Var exact 0.018660578209209914 frame formula 0.018660578209209917 MC 0.018597534120321127
S - diag(s2) - E 2.7755575615628914e-17
excess 0.012385681080223646 formula 0.012385681080223651 first-order diag term 0.007579622181818497  sum lam^2 s2 E_ii 0.007579622181818498
eigmin(Sigma^mb - Sigma^ULA) 0.003356885787190886  = lyapunovVia(h^2t^2 C)? 2.7755575615628914e-17
```

## GPT-6 Astra v1

Verbatim in `gpt_minibatch_fluctuation_v1.md` (prompt in `gpt_minibatch_fluctuation_v1_prompt.md`). Summary:
- **A, B correct; C's algebra correct, its first-order reading corrected.** The series identity needs no positivity; for `N ⪰ 0` every summand is
  nonnegative so `xᵀ diagLyap x ≥ xᵀNx`, i.e. the stronger `diagLyapunov a N − N ⪰ 0` (hence PSD/PD preservation and `lyapunovVia U a N ⪰ N`
  after conjugation); `2h·1 ≻ 0`, `h²t²C ⪰ 0` with no sign assumption on `t`. The fixed-point equation alone is circular as a positivity proof;
  a Schur-product proof essentially recovers the series. Use the scalar quadratic-form series, not matrix-valued infinite sums.
- **B**: symmetry of `Σ̂` turns `Σ̂ᵢⱼΣ̂ⱼᵢ` into a square; if the statistic is `tQ`, multiply by `t²`.
- **C corrections**: with `αᵢ = (ht²/2)Ĉᵢᵢ`, `Σ̂ᵢᵢ = σᵢ²(1 + αᵢ)`: the mean contribution scales by `1 + αᵢ` but the diagonal variance contribution
  by `(1 + αᵢ)² = 1 + 2αᵢ + O(αᵢ²)` — **twice** the relative increment (the standard deviation has the same factor). "Off-diagonal noise enters
  only at second order" holds for the *centred* variance; the noncentral term `∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼEᵢⱼ` contains off-diagonal entries at first order.
  "First order" means `C ↦ εC` at fixed `h, t, ρ`, not an asymptotic in `h`. **Do not** infer "hence the long-run variance / needed steps
  inflate" — marginal variance does not determine integrated autocovariance; that needs the lag formulas of tides 102–103.
- **Lean**: use `posDef_iff_dotProduct_mulVec`/`posSemidef_iff_dotProduct_mulVec`; order: Hermitian-ness, summability + series,
  `diagLyapunov_sub_posSemidef`, PSD/PD preservation, conjugation transport (orientation: `BᴴMB` with `B = Uᵀ`; injectivity of `Uᵀ.mulVec`
  from `UUᵀ = 1`), `minibatchNoise_posDef`, `Σ^{mb} ≻ 0`; entrywise symmetry needs no denominator facts; prove the zeroth summand equals `xᵀNx`
  separately; use nonnegativity only for the whole quadratic-form summand.
- **Cheap additions**: `Σ^{mb} ⪰ N^{mb}` via the fixed point once PSD is known (`Σ − N = AΣAᵀ ⪰ 0`), and for `H ⪰ 0` `tr(HΣ) ≥ tr(HN)`; D
  (`Var^{mb} ≥ Var^{ULA}`) via one reusable lemma `tr(BE) ≥ 0` for PSD `B, E` (`ΔVar = tr(HΣ₀HE) + ½tr(HEHE) + (Hm)ᵀE(Hm) ≥ 0`, any symmetric `H`).
- **Vote: A+B+C with the factor-of-two and noncentral caveats corrected; covariance order and D if the PSD trace-product lemma is cheap;
  defer long-run claims to a separate temporal proof.**

Adopted: A+B+C with GPT's corrected reading in the docstrings and note (`(1+α)²` vs `1+α`; centred vs noncentral); the stronger
`diagLyapunov_sub_posSemidef`; `Σ^{mb} − Σ^{ULA} ⪰ 0` via linearity. Deferred: `Σ^{mb} ⪰ N^{mb}`, the PSD trace-product lemma and D, any
long-run (temporal) inflation statement.

## Vote
- Claude: A+B+C
- GPT-6 Astra: A+B+C (+ covariance order / D if cheap)
