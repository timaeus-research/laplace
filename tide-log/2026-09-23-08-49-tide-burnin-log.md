# Tide: burnin-log

**Direction (user):** auto mode — "Continue with what you think best, don't stop"; chosen: E4 at the anchored scaling — the scaled ULA burn-in transient of tide 99's budget vanishes along any schedule `k(t)` with `k(t) → ∞` and `t·r^{2k(t)} → 0` (`r` a uniform stability bound), the logarithmic schedule `k(t) = ⌈κ log t⌉` satisfies this for `κ > 1/(2 log(1/r))`, and hence at the β-scaled step the sampled scaled statistic after `⌈κ log t⌉` steps converges to the localised energy plus the step-size bias: burn-in grows only logarithmically in `t`.
**Seabed:** laplace, commit 4cc1e5c (tide 107 `fulllaw-llc` landed)
**Started:** 2026-09-23T08:50Z

## Candidates v1 (Claude)

Anchored model in the E2 frame: `pᵢ = tλᵢ + g`, `ρᵢ(t) = 1 − (η/t)pᵢ`, `σᵢ² = 1/(pᵢκᵢ)`, `m̂ᵢ = gŵᵢ/pᵢ`, start `x₀` fixed (`x̂₀ = Qᵀx₀`); tide 99's burn-in term
`Burn(t, k) = (t/2)∑ᵢλᵢρᵢ^{2k}σᵢ² − (t/2)∑ᵢλᵢ[(m̂ᵢ + ρᵢ^k(x̂₀ᵢ − m̂ᵢ))² − m̂ᵢ²]` (the exact difference between the scaled `k`-step energy and its stationary value, sign as in `ulaAnchored_llc_budget`); `r∞ = maxᵢ|1 − ηλᵢ| < 1`.
- **A** (general vanishing criterion, `burnScaled_tendsto_zero`): for any `k : ℝ → ℕ` with `Tendsto k atTop atTop` and `Tendsto (t·r^{2k(t)}) atTop (𝓝 0)` for some `r ∈ (r∞, 1)`, `Burn(t, k(t)) → 0`. Proof: eventually `|ρᵢ(t)| ≤ r`; the three pieces are `λᵢ(tσᵢ²)ρᵢ^{2k}` (`tσᵢ² → 1/(λᵢ(1−ηλᵢ/2))`, `|ρ|^{2k} ≤ r^{2k} → 0`), `(t/2)λᵢρᵢ^{2k}dᵢ²` (`|·| ≤ (λᵢ/2)dᵢ²·t r^{2k} → 0`), `tλᵢρᵢ^k m̂ᵢ dᵢ` (`t m̂ᵢ → gŵᵢ/λᵢ`, `|ρ|^k ≤ r^k → 0`), with `dᵢ = x̂₀ᵢ − m̂ᵢ → x̂₀ᵢ`.
- **B** (the logarithmic schedule, `log_schedule_tendsto`): for `0 < r < 1` and `κ > 1/(2 log(1/r))`, `k(t) = ⌈κ log t⌉₊` has `k(t) → ∞` and `t·r^{2k(t)} → 0` (`r^{2⌈κ log t⌉} ≤ r^{2κ log t} = t^{2κ log r}`, so `t r^{2k} ≤ t^{1 + 2κ log r} → 0`).
- **C** (`burnScaled_log_tendsto_zero`): A ∘ B — `Burn(t, ⌈κ log t⌉₊) → 0` for every `κ > 1/(2 log(1/r))`, `r ∈ (r∞, 1)`: **burn-in of order `log t` suffices** for the scaled statistic.
- **D** (E2+E3+E4 at the schedule, `ulaAnchored_sampled_tendsto`): combining tide 99's budget `|t⟨L⟩_loc − t⟨½uᵀHu⟩_k − C₁′/t + (th/4)∑λᵢ/κᵢ − Burn(t,k)| ≤ K/t²` with `ulaScaledStep_bias_tendsto` and C: **`t⟨½uᵀHu⟩_{k(t)} − t⟨L⟩_loc → (η/4)∑ᵢλᵢ/(1−ηλᵢ/2)`** — after `⌈κ log t⌉` steps at the β-scaled step the sampled scaled statistic converges to the exact localised energy plus the step-size bias (sign corrected from the consult prompt, where I had written `−`).
- **E** (optional, necessity): for `κ < 1/(2 log(1/r∞))` and `x̂₀ ≠ 0` the burn-in does not vanish (the check shows it growing).

## Numerical check

`numcheck108.py` (`λ = (1, 2.5, 0.7)`, `η = 0.3`, `g = 0.7`, fixed `x̂₀`): `r∞ = 0.79`, `κ_crit = 2.12`; at `κ = 1.5κ_crit` the burn-in falls `−6.3e-2 → −5.8e-5` over `t = 10 … 10⁶` with `t r^{2k} → 1e-3`; at `κ = 0.7κ_crit` it does not vanish (`−0.6 → −3.2`, `t r^{2k}` growing).
```
r_inf 0.79  kappa_crit = 1/(2 log(1/r)) = 2.121139700813746
kappa = 3.182 (above threshold)
  t=      10 k=  8 Burn=-6.278e-02  t r^(2k)=2.302e-01
  t=     100 k= 15 Burn=-1.226e-02  t r^(2k)=8.488e-02
  t=    1000 k= 22 Burn=-2.675e-03  t r^(2k)=3.130e-02
  t=   10000 k= 30 Burn=-4.982e-04  t r^(2k)=7.205e-03
  t=  100000 k= 37 Burn=-1.644e-04  t r^(2k)=2.657e-03
  t= 1000000 k= 44 Burn=-5.766e-05  t r^(2k)=9.799e-04
kappa = 1.485 (below threshold)
  t=      10 k=  4 Burn=-6.318e-01  t r^(2k)=1.517e+00
  t=     100 k=  7 Burn=-9.813e-01  t r^(2k)=3.688e+00
  t=    1000 k= 11 Burn=-7.671e-01  t r^(2k)=5.595e+00
  t=   10000 k= 14 Burn=-1.286e+00  t r^(2k)=1.360e+01
  t=  100000 k= 18 Burn=-1.456e+00  t r^(2k)=2.063e+01
  t= 1000000 k= 21 Burn=-3.161e+00  t r^(2k)=5.016e+01
```

## GPT-6 Astra v1

Full response in `gpt_burnin-log_v1.md` (prompt in `gpt_burnin-log_v1_prompt.md`). Summary:

- **A–C correct.** Burn(t,k) = ½∑λᵢ(tσᵢ²)ρᵢ^{2k} − (t/2)∑λᵢρᵢ^{2k}dᵢ² − ∑λᵢ(tm̂ᵢ)ρᵢ^k dᵢ with tσᵢ², tm̂ᵢ, dᵢ eventually bounded and |ρᵢ(t)| ≤ r eventually, so |Burn| ≤ C₁r^{2k} + C₂tr^{2k} + C₃r^k. The hypothesis k(t) → ∞ is redundant given 0 < r < 1 and t r^{2k(t)} → 0 (for t ≥ 1, r^{2k} ≤ t r^{2k}); harmless to keep. The logarithmic schedule qualifies exactly when κ > 1/(2 log(1/r)); a helper lemma "ceiling to real power" (t r^{2⌈κ log t⌉} ≤ t^{1+2κ log r} for t > 1) is the clean route.
- **D has the wrong sign as first drafted.** From the budget, t⟨½uᵀHu⟩_k − t⟨L⟩_loc = (th/4)∑λᵢ/κᵢ − C′/t − Burn + O(t⁻²), so the limit is **+(η/4)∑ᵢλᵢ/(1−ηλᵢ/2)** (the sampled scaled statistic exceeds the exact localised energy by the step-size bias). Corrected in Candidates before formalising.
- **E is false as stated.** With a fixed start the relevant contraction rate is the *active-mode* rate r_* = max{|1−ηλᵢ| : x̂₀ᵢ ≠ 0} (or the mode where the mean piece survives), not r∞; the sharp threshold is κ_* = 1/(2 log(1/r_*)), and the mean term makes the criterion depend on the start. Present as a remark, not a theorem.
- Suggested corollaries: total iteration count ⌈κ log t⌉ + n_ε; the unscaled statistic needs only k → ∞. Recorded as follow-ups.

## Vote
- Claude: A + B + C + D (sign-corrected), E as a remark
- GPT-6 Astra: "ship A–C and sign-corrected D, add qualified iteration-count and unscaled corollaries, and present active-mode sharpness as a remark rather than formalizing E now"
