# Tide: burnin-average

**Direction (user):** auto mode — E4: the non-stationary autocovariance of the ULA LLC statistic from a fixed start and the fixed-`n` post-burn-in average (GPT's suggested follow-up to tide 110).
**Seabed:** laplace, commit 8732fd8 (tide 102 `ULAAutocovariance` (`condEnergy`, Wick lemmas), tide 108 `BurnInLog`, tide 110 `MSELog`)
**Started:** 2026-09-23-10-37 UTC

## Candidates v1 (Claude)

Setting as in tides 108/110: ULA on `P_t = tH + gI` at `h = η/t`, from a fixed `x₀`; `s`-step law Gaussian with frame variances
`v_{s,i} = σᵢ²(1 − ρᵢ^{2s})` and means `μ_{s,i} = m̂ᵢ + ρᵢ^s(x̂₀ᵢ − m̂ᵢ)`; `q(u) = ½uᵀHu`; `αᵢ = 1 − ηλᵢ`, `aᵢ = 1 − ηλᵢ/2`. Tide 102 defined the
stationary autocovariance at kernel level as `Cov_π(q, condEnergy_ℓ)` with `condEnergy_ℓ(x) = E[q(X_ℓ) | X_0 = x]` (the Markov identification
is the prose bridge). The same device from a fixed start:

- **A** (`burnAutoCov`, `burnAutoCov_eq`): `Cov_s(q, condEnergy_ℓ)` under the `s`-step law (`s ≥ 1`) equals
  `½∑ᵢλᵢ²v_{s,i}²ρᵢ^{2ℓ} + ∑ᵢλᵢ²v_{s,i}ρᵢ^ℓμ_{s,i}μ_{s+ℓ,i}` for every lag `ℓ` (lag 0 is tide 105's `k`-step variance).
- **B** (`ulaAnchored_autoCov_schedule_tendsto`): along a schedule with `k(t) → ∞`, `t·r^{2k(t)} → 0`, for each fixed lag `ℓ`,
  `t²Cov_{k(t)}(q, condEnergy_ℓ) → c_ℓ^∞ := ½∑ᵢaᵢ⁻²αᵢ^{2ℓ}` (the stationary scaled autocovariance of tide 103), the start's memory being
  `o(1)` at this scale.
- **C** (`ulaAnchored_sampled_schedule_tendsto`): tide 108's mean statement for a general schedule (so that it applies at `k(t) + a`).
- **D** (`avgVar`, `avgBias`, `ulaAnchored_avgVar_log_tendsto`, `ulaAnchored_avgBias_log_tendsto`, `ulaAnchored_avg_mse_log_tendsto`): for the average
  of `n` consecutive post-burn-in draws `q(X_{k+a})`, `a < n`, the kernel-level variance
  `(1/n²)(∑_{a<n}Cov_{k+a}(q,q) + 2∑_{j<n}∑_{a<n−(j+1)}Cov_{k+a}(q, condEnergy_{j+1}))` satisfies
  `t²·avgVar → (1/n²)(n c₀^∞ + 2∑_{j<n}(n−(j+1))c^∞_{j+1}) = ½∑ᵢaᵢ⁻²F_n(αᵢ²)`, `F_n(z) = (n + 2∑_{j<n}(n−(j+1))z^{j+1})/n²`; the scaled
  bias of the average → `b_η`; hence the scaled MSE of the `n`-draw average → `b_η² + ½∑ᵢaᵢ⁻²F_n(αᵢ²)`.
- **E** (`Fn_le_one`, `Fn_ge_inv`): `1/n ≤ F_n(z) ≤ 1` for `z ∈ [0,1)`: correlated draws are worth at least `1/n`-th and at most one independent draw.

## Numerical check

`numcheck111.py` (`λ = (1, 2.5, 0.7)`, `η = 0.3`, `g = 0.7`, random `ŵ, x̂₀`, `κ = 1.5κ_crit`, `n = 5`; the closed form is checked against a Monte
Carlo simulation of the frame chain, 4·10⁵ paths):
```
closed form vs Monte Carlo (t=50, s=6): lag  closed   MC
   0   0.00207  0.00206
   1   0.00090  0.00090
   2   0.00049  0.00049
   4   0.00016  0.00016
limits: c_l^inf = ½∑a⁻²α^{2l}:  [np.float64(2.59624), np.float64(0.80866), np.float64(0.41429), np.float64(0.23347)]  avg var(n=5) -> 0.92557  MSE -> 1.12529
  t=   1e+02 k= 15  t^2 c_l = [np.float64(2.60604), np.float64(0.8067), np.float64(0.40945), np.float64(0.22784)]  t^2 avgVar=0.91727  t*avgBias=0.44601  t^2 MSE=1.11620
  t=   1e+03 k= 22  t^2 c_l = [np.float64(2.61166), np.float64(0.81702), np.float64(0.41878), np.float64(0.23572)]  t^2 avgVar=0.92845  t*avgBias=0.44948  t^2 MSE=1.13048
  t=   1e+04 k= 30  t^2 c_l = [np.float64(2.60075), np.float64(0.8113), np.float64(0.41582), np.float64(0.23434)]  t^2 avgVar=0.92671  t*avgBias=0.44775  t^2 MSE=1.12718
  t=   1e+05 k= 37  t^2 c_l = [np.float64(2.59822), np.float64(0.80987), np.float64(0.41502), np.float64(0.2339)]  t^2 avgVar=0.92614  t*avgBias=0.44730  t^2 MSE=1.12622
  t=   1e+06 k= 44  t^2 c_l = [np.float64(2.59703), np.float64(0.80915), np.float64(0.41459), np.float64(0.23365)]  t^2 avgVar=0.92581  t*avgBias=0.44706  t^2 MSE=1.12567
```

## GPT-6 Astra v1

Full response in `gpt_burnin-average_v1.md` (prompt in `gpt_burnin-average_v1_prompt.md`). Summary:

- **A–E correct** (fixed `n ≥ 1`, schedule hypotheses in B). `Cov(q(X_s), q(X_{s+ℓ})) = Cov_{law(X_s)}(q, P^ℓq)` by conditional expectation
  (Markov property only, no stationarity); in one frame coordinate `Y = ρ^ℓX + (1−ρ^ℓ)m̂ + ε` gives `Cov(X², Y²) = 2Cov(X,Y)² + 4EX·EY·Cov(X,Y)`
  with `Cov(X,Y) = v_sρ^ℓ`, which is the closed form; it also holds at `s = 0` (both sides vanish).
- **B**: the memory term must be checked at the `t²` scale: `t²λ²v_sρ^ℓμ_sμ_{s+ℓ} = λ²(tv_s)ρ^ℓ(tμ_sμ_{s+ℓ})`, so it is `tμ_sμ_{s+ℓ} → 0` that matters
  (our expansion `(tm̂)m̂ + (tm̂)(ρ^{s+ℓ}+ρ^s)d + (tρ^{2s})ρ^ℓd²` does exactly that).
- **D**: the pair bookkeeping is right (`b = a + j + 1`, `a < n − (j+1)`); record the two prose-bridge identities
  `Var((1/n)∑q(X_{k+a})) = avgVar` and `E[((1/n)∑q − ⟨L⟩_loc)²] = avgVar + avgBias²` explicitly as not machine-checked.
- **E** extends to `z ∈ [0,1]`; `F_n(0) = 1/n`, `F_n(1) = 1`; strict for `n > 1`, `0 < z < 1`.
- Cheap additions (adopted): the IAT bound `F_n(z) ≤ (1+z)/(n(1−z))`, hence `V_η/n ≤ W_{η,n} ≤ min{V_η, L_η/n}` for the limiting variance
  coefficient; monotonicity of `F_n` in `z`; endpoints `F_1 = 1`, `F_n(1) = 1`. Deferred: the exact identity
  `F_n(z) = (1+z)/(n(1−z)) − 2z(1−z^n)/(n²(1−z)²)` and `nF_n(z) → (1+z)/(1−z)` (recovering tide 103's `L_η`); the independent-replica comparison
  `b_η² + V_η/n` (same prose bridge).
- **Wording**: "for every fixed `n ≥ 1`, the average of `n` consecutive post-burn-in energy observations has scaled MSE converging to
  `b_η² + ½∑ᵢaᵢ⁻²F_n(αᵢ²)`; averaging multiplies each mode's limiting variance by `F_n(αᵢ²) ∈ [1/n, 1]` and does not reduce the discretisation bias".
  Caveats: sufficient burn-in `κ > 1/(2 log(1/r))` (not just "logarithmic"); fixed `n`, no growing-window claim; the `F_n` comparison is a
  statement about the limit (the finite-`t` memory term need not be nonnegative); the trajectory/MSE bridge is prose.

## Candidates v2 (Claude, adopting the additions)

- **F** (`lagWeight_one_draw`, `lagWeight_at_one`, `lagWeight_zero`, `lagWeight_mono`, `lagWeight_le_iat`): `F_1 = 1`, `F_n(1) = 1`, `F_n(0) = 1/n`,
  monotone in `z`, and the IAT bound `F_n(z) ≤ (1+z)/(n(1−z))`.

## Vote
- Claude: A + B + C + D + E, plus F
- GPT-6 Astra: "Formalise A, B, C, D, E now … prioritise the endpoint/regression lemmas, the IAT bound, and monotonicity"

## Result

Commit `437a0a5` on `tide/burnin-average`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Multi/BurnInAverage.lean` (     524 lines).
A–E as voted plus the GPT-suggested lag-weight lemmas (F).
Lemmas: `burnAutoCov` (def), `avgVar` (def), `burnAutoCov_zero_eq`, `burnAutoCov_eq_of_pos`, `burnAutoCov_eq`, `ulaAnchored_burnAutoCov`,
`ulaAnchored_autoCov_schedule_tendsto`, `lagWeight` (def), `sum_range_sub_succ`, `lagWeight_le_one`, `inv_le_lagWeight`, `lagWeight_zero`,
`lagWeight_one_draw`, `lagWeight_at_one`, `lagWeight_mono`, `lagWeight_le_iat`, `avgLimit_eq_lagWeight`, `ulaAnchored_avgVar_schedule_tendsto`,
`ulaAnchored_sampled_schedule_tendsto`, `ulaAnchored_avg_mse_log_tendsto`.

Surprises: three short build rounds. The Wick computation of tide 102 carried over verbatim to the non-stationary law once the tilt was unfolded to
`Σ_s⁻¹ *ᵥ μ_s` (so `tiltMean_mulVec_self` applies) and `transpose_mulVec_burnInMeanAnch` was added to the frame simp set; the one real
obstacle was `ring`'s inability to identify `α^(2j+2)` with `(α²)^(j+1)` for a compound base after `mul_add` had distributed the exponent, fixed
by ordering the simp calls. GPT confirmed the pair bookkeeping and insisted the memory term be checked at the `t²` scale (`tμ_sμ_{s+ℓ} → 0`),
which is what the expansion does.
