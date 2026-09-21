# Tide: burnin-envelope

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the spectrum-free E4 error budget for the LLC (follow-up flagged by GPT-6 Astra in tide `llc-mse`).
**Seabed:** laplace, main after `autocorrelation-time` (c03b14e; `LLCMSE.lean` from tide `llc-mse` on main)
**Started:** 2026-09-21 (UTC, see filename)

## Context

Tide `llc-mse` proved the three-term RMS bound for the pooled LLC against `d/2` in spectral form (`llc_rel_rms_le`):
`√MSE/(d/2) ≤ 2√envelope/d + (1/d)∑ᵢ (h pᵢ/2)/(1 − h pᵢ/2) + (1/(dN))∑ᵢ ρᵢ^{2(b+1)}/((1 − ρᵢ²)(1 − h pᵢ/2))`, `ρᵢ = 1 − h pᵢ`,
`envelope = 1/(2CN)∑ᵢ (1 + ρᵢ²)/((1 − ρᵢ²)(1 − h pᵢ/2)²)`. GPT-6 Astra asked for the spectrum-free corollary in the note's variables
`h pmax`, `h pmin`, `κ`, and pointed out that the burn-in term needs a *coupled* monotonicity argument: as a function of `ρ` it is
`2ρ^{2b}/(1−ρ) · (ρ/(1+ρ))²`, each factor increasing on `[0, 1)`, whereas its denominator `(1−ρ²)(1+ρ)/2` is not monotone by itself.
The note's E4/Summary recipe speaks in exactly these terms ("set `lr = 0.1/pmax`; run at least `20κ` steps per chain").

## Candidates v1 (Claude)

Write `r = 1 − h pmin` (the flattest direction's AR(1) coefficient) and assume `pmin ≤ pᵢ ≤ pmax`, `0 < h pmin`, `h pmax ≤ 1`.

**A. Per-direction monotonicity.**
```
tau_mono        : 0 ≤ ρ ≤ ρ' < 1 → (1+ρ²)/(1−ρ²) ≤ (1+ρ'²)/(1−ρ'²)
excess_mono     : 0 ≤ x ≤ x' < 1 → x/(1−x) ≤ x'/(1−x')
burnin_term_eq  : ρ^{2(b+1)}/((1−ρ²)(1+ρ)/2) = 2ρ^{2b}/(1−ρ) · (ρ/(1+ρ))²
burnin_term_mono: 0 ≤ ρ ≤ ρ' < 1 → ρ^{2(b+1)}/((1−ρ²)(1+ρ)/2) ≤ ρ'^{2(b+1)}/((1−ρ'²)(1+ρ')/2)
```

**B. The three sums, spectrum-free.**
```
inflation_sum_le_free   : ½∑ᵢ (h pᵢ/2)/(1 − h pᵢ/2) ≤ (d/2) · (h pmax/2)/(1 − h pmax/2)
shortfall_bd_sum_le_free: ½∑ᵢ ρᵢ^{2(b+1)}/(N(1−ρᵢ²)(1 − h pᵢ/2)) ≤ (d/2) · r^{2(b+1)}/(N(1−r²)(1 − h pmin/2))
envelope_sum_le_free    : 1/(2CN)∑ᵢ (1+ρᵢ²)/((1−ρᵢ²)(1 − h pᵢ/2)²) ≤ d/(2CN) · (1+r²)/(1−r²) / (1 − h pmax/2)²
```
(the autocorrelation factor `(1+ρ²)/(1−ρ²)` is largest on the flattest direction, the step factor `1/(1 − h p/2)²` on the stiffest; the
product is bounded by the product of the two maxima — the envelope term itself is *not* monotone in `ρ`, as the numerical check shows).

**C. The spectrum-free three-term bound** (`llc_rel_rms_le_free`): on the ULA chain with Gaussian noise,
```
√E(LLĈ − d/2)² / (d/2) ≤ 2√(d/(2CN) · τ(r²)/(1 − h pmax/2)²)/d + (h pmax/2)/(1 − h pmax/2) + r^{2(b+1)}/(N(1−r²)(1 − h pmin/2))
```
with `τ(r²) = (1+r²)/(1−r²)`: the note's recipe in closed form — a Monte Carlo term `≈ √(2τ_flat/(d·CN))`, the ULA inflation `≈ h pmax/2`,
and a burn-in term decaying like `r^{2b}`, with `τ_flat ≈ 2/(h pmin) = 20κ` at `h pmax = 0.1` (`iat_flat_twenty_kappa`).

Vote intention: A+B+C.

## Numerical check

`numcheck37.py` (`d = 10`, log-uniform `κ = 100`, `h pmax = 0.1`, `C = 4`, `N = 1000`, `b = 100`):
```
spectral three-term bound = 0.20281   spectrum-free bound = 0.69686   ok=True
burn-in term monotone increasing in rho: True  envelope term monotone: True   [τ(ρ²) alone; the full envelope term is not]
identity burn = 2 rho^{2b}/(1-rho) (rho/(1+rho))^2, max err: 5.9e-12
x/(1-x) monotone: True
```
The spectrum-free bound dominates the spectral one (by a factor ≈ 3.4 here — the price of replacing every direction by the flattest).

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_burnin_envelope_v1.md`. Summary: A–C correct with `h > 0` stated explicitly (it is); the burn-in factors are nondecreasing on `[0,1)` (the power factor is constant at `b = 0`); the envelope's product-of-maxima bound is valid but not optimal — the per-direction envelope term `f(ρ) = 4(1+ρ²)/((1−ρ)(1+ρ)³)` has a single interior minimum, so `f(ρᵢ) ≤ max(f(s), f(r))` with `s = 1 − h pmax`, and for `h pmax ≤ 1/2` (the `0.1` recipe) `f(r)` alone suffices (deferred). **Factor-of-two correction**: with `a = h pmin = 1/(10κ)`, `τ(r) = (2−a)/a = 20κ − 1` is the autocorrelation time of the chain, while the envelope uses `τ(r²) = (2 − 2a + a²)/(2a − a²) ≈ 10κ − 1/2`, that of the squared chain; `τ(r)/τ(r²) = (1+r)²/(1+r²) → 2`. So the note's `20κ` is one chain autocorrelation time or two squared-chain ones. Cheap additions taken up: the ESS-form Monte Carlo term `√(2τ(r²)/(d·CN))/(1 − h pmax/2)` (envelope-based ESS `CN/τ(r²)`); the `κ`-specialisation (step factor `20/19`, inflation `1/19`) left to the SRI note.

## Vote
- Claude: A+B+C (+ the ESS-form restatement)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.

## Result

Committed on `tide/burnin-envelope` at cd77779 (`lake build` clean, `scripts/sorries`: 0 sorry, 0 axiom, 0 native_decide). New module `Laplace/Sampler/BurnInEnvelope.lean` (316 lines): `tau_mono`, `excess_mono`, `burnin_term_eq`, `div_one_add_mono`, `burnin_term_mono`, `inflation_sum_le_free`, `shortfall_bd_sum_le_free`, `envelope_sum_le_free`, `llc_rel_rms_le_free`, `monte_carlo_term_eq`, `llc_rel_rms_le_free'`.

Surprises: (i) the envelope term `(1+ρ²)/((1−ρ²)(1−hp/2)²)` is not monotone in `ρ` (the numerical check caught the first draft's claim) — the product-of-maxima bound is the honest spectrum-free statement, and GPT located the sharper `max(f(s), f(r))`; (ii) GPT's factor-of-two correction: the note's `20κ` is the chain's autocorrelation time, the variance envelope uses the squared chain's `≈ 10κ`; (iii) three hypotheses (`0 ≤ x` in `excess_mono`, `0 ≤ ρ` in the identity, `hp` in the inflation sum) were redundant and caught by the linter.
