# Tide: minibatch-longrun

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: the temporal E8+E5 piece GPT asked for in tide 104 — the `k`-step law of the constant-noise (minibatch) SGLD chain from a start (`Σ_k = Σ^{mb} − A^kΣ^{mb}(Aᵀ)^k`, the covariance-step iterate from 0), its positive definiteness for `k ≥ 1` via the finite geometric sum, its energy mean, the stationary energy autocovariance `Cov(Y₀, Y_ℓ) = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²ρⱼ^{2ℓ} + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼρⱼ^ℓ` and the long-run variance under minibatch noise, with the full frame covariance `Ŝ`.
**Seabed:** laplace, commit 22f025b (tide 104 `minibatch-fluctuation` landed)
**Started:** 2026-09-23T07:58Z

## Candidates v1 (Claude)

Frame `U` diagonalising `P` (`p`) and `H` (`λ`), `A = ulaStep P h = U diag(ρ) Uᵀ`, `ρᵢ = 1 − hpᵢ`, `N = 2h·1 + h²t²C` (`C ⪰ 0`), `N̂ = UᵀNU`, `Σ = lyapunovVia U ρ N = U Ŝ Uᵀ` with `Ŝ = diagLyapunov ρ N̂` (`Ŝᵢⱼ = N̂ᵢⱼ/(1−ρᵢρⱼ)`), `m̂ = Uᵀm`, `Y = ½uᵀHu`.
- **A** (the `k`-step law): `mbBurnInCov k := Σ − A^kΣ(Aᵀ)^k` is the `k`-th covariance-step iterate from `0` (`mbBurnInCov_eq_iterate`, from the seabed's `covStep_iterate_zero` and the fixed-point characterisation); in the frame `mbBurnInCov k = U·(Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k))·Uᵀ` (`mbBurnInCov_eq_conj_frame`) with `Ŝᵢⱼ(1 − ρᵢ^kρⱼ^k) = N̂ᵢⱼ∑_{r<k}(ρᵢρⱼ)^r`, so `xᵀ(·)x = ∑_{r<k}(ρ^r∘x)ᵀN̂(ρ^r∘x) ≥ xᵀN̂x > 0`: **`mbBurnInCov k ≻ 0` for `k ≥ 1`** (`mbBurnInCov_posDef`). The `k`-step law is the tilted Gaussian with this covariance and the mean `m + A^k(x₀ − m)` (`burnInMeanAnch`).
- **B** (energy from a start): `⟨½uᵀHu⟩_k = ½∑ᵢλᵢŜᵢᵢ(1 − ρᵢ^{2k}) + ½∑ᵢλᵢ(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ))²` (`mbBurnIn_energy_frame`; only the frame diagonal of `Ŝ` enters), hence the conditional energy `mbCondEnergy k x₀ = ½x₀ᵀB_kx₀ + b_k·x₀ + c_k` with tide 102's `B_k = U diag(λρ^{2k}) Uᵀ`, `b_k = U diag(λρ^k(1−ρ^k)) Uᵀ m` and a new constant (`mbCondEnergy_eq`).
- **C** (autocovariance): `mbAutoCov ℓ := Cov_{N(m,Σ)}(Y, mbCondEnergy ℓ ·)`, **`mbAutoCov ℓ = ½∑ᵢⱼλᵢλⱼŜᵢⱼ²ρⱼ^{2ℓ} + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼρⱼ^ℓ`** at every lag (`mbAutoCov_eq`; lag 0 = tide 104's variance), via tide 102's covariance-shift and mixed Wick and tide 104's non-diagonal frame lemmas (`tr(HΣB_ℓΣ) = ∑ᵢⱼλᵢŜᵢⱼλⱼρⱼ^{2ℓ}Ŝⱼᵢ`, `(Hm)ᵀΣ(B_ℓm + b_ℓ) = ∑ᵢⱼλᵢm̂ᵢŜᵢⱼλⱼρⱼ^ℓm̂ⱼ`). For diagonal `Ŝ` this is tide 102's formula.
- **D** (long-run variance): `mbLongRunVar := mbAutoCov 0 + 2∑'_{ℓ≥0} mbAutoCov(ℓ+1)` **`= ½∑ᵢⱼλᵢλⱼŜᵢⱼ²(1+ρⱼ²)/(1−ρⱼ²) + ∑ᵢⱼλᵢλⱼm̂ᵢm̂ⱼŜᵢⱼ(1+ρⱼ)/(1−ρⱼ)`** (`mbLongRunVar_eq`), summability (`mbAutoCov_summable`).
- **E** (optional): with `Ŝᵢⱼ = σᵢ²[i=j] + Eᵢⱼ` (tide 104), the centred long-run excess `½∑ᵢⱼλᵢλⱼ(2σᵢ²[i=j]Eᵢⱼ + Eᵢⱼ²)(1+ρⱼ²)/(1−ρⱼ²) ≥ 0` (λ > 0, `Eᵢᵢ ≥ 0`): minibatch noise inflates the centred long-run variance; the mean part's sign is not determined by these formulas.

## Numerical check

`numcheck105.py` (3D random frame, `t = 20`, `g = 0.7`, `h = 0.3/t`, random PSD `C` of scale 0.05, 2·10⁶ chains with noise `N`): the `k`-step covariance iterate equals `Σ − A^kΣA^kᵀ` (6e-17), its frame entries equal `Ŝᵢⱼ(1−ρᵢ^kρⱼ^k) = N̂ᵢⱼ∑_{r<k}(ρᵢρⱼ)^r` and it is positive definite; the energy after `k = 3` steps: exact = frame (0.185601); autocovariances closed = exact (mixed Wick) = Monte Carlo at lags 0–6; `τ²` series = closed (0.037970), against the ULA `τ²` 0.014214 (ratio 2.67).
```
k-step cov iterate vs Sigma - A^k Sigma A^kT: 5.551115123125783e-17
frame entries S_ij(1-rho_i^k rho_j^k): 4.163336342344337e-17  = Nh sum_{r<k}: 4.163336342344337e-17  eigmin 0.04849939319559805
energy after k steps exact 0.18560113802323971 frame 0.18560113802323977
lag  closed        exact        MC
  0  1.639215e-02 1.639215e-02 1.636024e-02
  1  4.953553e-03 4.953553e-03 4.923397e-03
  2  2.514956e-03 2.514956e-03 2.507939e-03
  3  1.402080e-03 1.402080e-03 1.402599e-03
  4  7.987311e-04 7.987311e-04 8.027226e-04
  5  4.606682e-04 4.606682e-04 4.495453e-04
  6  2.683815e-04 2.683815e-04 2.689921e-04
tau2 series 0.037970404549470885 closed 0.03797040454947089  ULA tau2 0.014214201918326203  ratio 2.6713004900061326
```

## GPT-6 Astra v1

Verbatim in `gpt_minibatch_longrun_v1.md` (prompt in `gpt_minibatch_longrun_v1_prompt.md`). Summary:
- **A–D correct** (Gaussian innovations, `|ρᵢ| < 1`, shared frame). `Σ_k = Σ − A^kΣ(Aᵀ)^k = ∑_{r<k}A^rN(Aᵀ)^r`, PD for `k ≥ 1`; the `k`-step law
  `N(m_k, Σ_k)` as the tilted Gaussian `(Σ_k⁻¹, Σ_k⁻¹m_k)` for `k ≥ 1`, `k = 0` separately as `δ_{x₀}` (done: `if k = 0`). Only `c_k` changes
  between ULA and minibatch (same drift). **The asymmetric `ρⱼ^{2ℓ}`/`ρⱼ^ℓ` is correct**; prove it first and give the symmetrised form
  `¼∑λλŜ²(ρᵢ^{2ℓ}+ρⱼ^{2ℓ}) + ½∑λλm̂m̂Ŝ(ρᵢ^ℓ+ρⱼ^ℓ)` as a corollary (swap `i,j`, `Ŝ` symmetric; no reversibility needed — the chain is
  generally non-reversible when `AΣ ≠ ΣA`). Do **not** replace the quadratic lag factor by `ρᵢ^ℓρⱼ^ℓ`. `Cov_π(q, K^ℓq) = Cov(Y₀, Y_ℓ)` for the
  stationary chain by conditioning (not merely a proxy); the summed autocovariances give `n·Var(Ȳ_n) → τ²` (a CLT is a separate theorem).
- **Scaling (E5+E8)**: with `P = tH`, `h = η/t`: `Ŝᵢⱼ = (2ηδᵢⱼ/t + η²Ĉᵢⱼ)/(η(λᵢ+λⱼ−ηλᵢλⱼ))`, so for fixed `C` the minibatch part is `O(1)` against the
  ULA `σᵢ² = 1/(tλᵢ(1−ηλᵢ/2))`; `τ²_{mb} = Θ(1)`, `t²τ²_{mb} = Θ(t²)`, i.e. `n = Θ(t²)` stationary steps for a fixed variance of the empirical
  average of `tq` — separate from the bias. Batch `B`: bounded scaled fluctuations and bounded additional scaled bias both need `B = Ω(t)`
  (with the mean `m = O(t^{−1/2})`, true for the anchored `O(1/t)` displacement); vanishing bias/recovery of ULA's `τ²` need `B/t → ∞`. Suggested
  sentence: "Linear batch growth controls both the scaled variance and the scaled minibatch bias, but generally leaves a nonzero bias and
  variance excess; superlinear batch growth removes the minibatch contribution. Longer runs reduce Monte Carlo variance, not stationary bias."
- **Lean**: finite innovation-sum identity and PD by separating `r = 0`; power/frame transport once; the covariance iterate + mean recursion do
  not alone *identify* a law (Gaussian closure under affine maps is the unformalised bridge); package integrability once; Frobenius-invariance
  lemma is right; prove the mixed covariance theorem then specialise `B_ℓ, b_ℓ`; summability before interchange; shifted powers for positive lags.
- **E, strengthened**: the mean-part excess **is** controllable — with `Q = h²t²Ĉ`, `Eᵢⱼ = Qᵢⱼ/(1−ρᵢρⱼ)`, `vᵢ = λᵢm̂ᵢ`, `f(r) = (1+r)/(1−r)`, the
  resolvent identity `(f(ρᵢ)+f(ρⱼ))/(2(1−ρᵢρⱼ)) = 1/((1−ρᵢ)(1−ρⱼ))` symmetrises `∑ᵢⱼvᵢvⱼEᵢⱼf(ρⱼ) = zᵀQz ≥ 0`, `zᵢ = vᵢ/(1−ρᵢ)` (works for negative
  stable `ρ`); the centred excess `2σᵢ²δᵢⱼEᵢᵢ + Eᵢⱼ²` is termwise nonnegative; hence **`τ²_{mb} ≥ τ²_{ULA}`** — the temporal inflation
  requested in tide 104. Special case `P = tH`: `Δτ²_{lin} = m̂ᵀĈm̂ = mᵀCm` exactly. Also `τ²_{lin} = vᵀ(1−R)⁻¹N̂(1−R)⁻¹v`.
- **Vote: A–D yes; prioritise full E via the resolvent identity and the diagonal recovery theorem, add symmetrisation cheaply, state the
  corrected scaling result with explicit mean and uniform-stability hypotheses (prose for now).**

Adopted: A–D; E in full (`mbLongRunVar_sub_ulaLongRunVar`, `ulaLongRunVar_le_mbLongRunVar` via the resolvent identity); the symmetrised
autocovariance (`mbAutoCov_eq_symm`). Deferred: the diagonal (`C = 0`) recovery theorem (immediate from the excess formula), the `P = tH`
special case `Δτ²_{lin} = mᵀCm`, the β-scaled `Θ(t²)` statement, `τ²_{lin} = vᵀ(1−R)⁻¹N̂(1−R)⁻¹v`.

## Vote
- Claude: A–D + E
- GPT-6 Astra: A–D + full E (+ symmetrisation, diagonal recovery)
