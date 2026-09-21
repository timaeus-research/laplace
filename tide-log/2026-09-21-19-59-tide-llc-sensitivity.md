# Tide: llc-sensitivity

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: "the LLC is the sensitive diagnostic" as a weighted Chebyshev inequality (E1, E5, E8).
**Seabed:** laplace, main after `autocorrelation-time` (c03b14e)
**Started:** 2026-09-21 (UTC, see filename)

## Context

The sanity note returns three times to one phenomenon. E1: "The LLC inherits this bias direction by direction … at `κ = 1000` only the few
stiff directions are inflated"; E5: "at `d = 50`, `t = 10⁴`, `lr pmax = 1` the sampled covariance is within 0.2% of `P⁻¹` in Frobenius norm
while the LLC is 44% high"; E8: "The whole-covariance trace inflates much less (`1.35×` where the LLC is `2.4×`) because the noise lands on
the stiff directions: as with the step-size bias, the LLC is the sensitive diagnostic and the Frobenius norm is not." The mechanism is a
weighting: a per-direction inflation `fᵢ` that grows with the stiffness `pᵢ` is averaged with weights `∝ pᵢ`-heavy for the LLC (each
direction counts `1/(1 − h pᵢ/2)`, or `1` in the pure Laplace limit) and `∝ 1/pᵢ`-heavy for the covariance trace (each direction counts its
variance). Seabed: `ula_llc`/`trace_mul_ulaCov` (`½ ∑ 1/(1 − h pᵢ/2)`), `minibatch_llc`/`trace_mul_minibatchCov`
(`½ ∑ (1 + h t² c̃ᵢ/2)/(1 − h pᵢ/2)`), `ulaCov_conj_eq_diagonal`, `minibatchCov_conj_diag`; Mathlib has Chebyshev's sum inequality for
`Monovary`ing functions with uniform weights (`Monovary.sum_mul_sum_le_card_mul_sum`) but not the weighted form needed here.

## Candidates v1 (Claude)

**A. Weighted Chebyshev.** For weights `vᵢ ≥ 0`, ratios `rᵢ`, and `f` monovarying with `r` (`rᵢ < rⱼ → fᵢ ≤ fⱼ`):
```
sum_mul_sum_le_of_monovary : (∑ vᵢ rᵢ)(∑ vᵢ fᵢ) ≤ (∑ vᵢ rᵢ fᵢ)(∑ vᵢ)
weighted_mean_le_of_monovary : (∑ vᵢ fᵢ)/(∑ vᵢ) ≤ (∑ vᵢ rᵢ fᵢ)/(∑ vᵢ rᵢ)      (v, r > 0)
```
(proof: `∑ᵢⱼ vᵢ vⱼ (rᵢ − rⱼ)(fᵢ − fⱼ) ≥ 0` termwise and equals twice the difference). In words: re-weighting an average by a factor
comonotone with `f` can only increase it.

**B. Traces in the eigenbasis** (small closures the instances need): `Uᵀ P⁻¹ U = diag(1/pᵢ)`, `tr P⁻¹ = ∑ 1/pᵢ`;
`tr Σ_ULA = ∑ 1/(pᵢ(1 − h pᵢ/2))`; `tr Σ_mb = ∑ (1 + h t² c̃ᵢ/2)/(pᵢ(1 − h pᵢ/2))`.

**C. The step-size instance (E1, E5).** With `fᵢ = 1/(1 − h pᵢ/2)` (increasing in `pᵢ`), `vᵢ = 1/pᵢ`, `rᵢ = pᵢ`:
```
ula_llc_inflation_ge_trace_inflation :
  tr Σ_ULA / tr P⁻¹  ≤  (½ ∑ 1/(1 − h pᵢ/2)) / (d/2)
```
the relative inflation of the covariance trace is at most that of the LLC, for every spectrum and step.

**D. The minibatch instance (E8).** With `fᵢ = 1 + h t² c̃ᵢ/2`, `c̃ᵢ = (UᵀCU)ᵢᵢ` the gradient-noise variance along direction `i`, under the
note's mechanism "the noise lands on the stiff directions" formalised as `Monovary c̃ p`:
```
minibatch_llc_inflation_ge_trace_inflation :
  tr Σ_mb / tr Σ_ULA  ≤  LLC_mb / LLC_ULA
```
and, without the monotonicity hypothesis, the reverse can hold (noise on the flat directions inflates the trace more than the LLC) — recorded
as a remark, not a theorem.

Vote intention: A+B+C+D.

## Numerical check

`numcheck34.py`:
```
d=  10 kappa=  100 h pmax=0.1: LLC rel inflation=1.0128  trace rel inflation=1.00204  ok=True
d=  10 kappa=  100 h pmax=0.5: LLC rel inflation=1.0744  trace rel inflation=1.01082  ok=True
d=  10 kappa=  100 h pmax=1.0: LLC rel inflation=1.1928  trace rel inflation=1.02403  ok=True
d=  50 kappa= 3600 h pmax=0.1: LLC rel inflation=1.0067  trace rel inflation=1.00011  ok=True
d=  50 kappa= 3600 h pmax=0.5: LLC rel inflation=1.0379  trace rel inflation=1.00055  ok=True
d=  50 kappa= 3600 h pmax=1.0: LLC rel inflation=1.0935  trace rel inflation=1.00117  ok=True
d=1000 kappa=  100 h pmax=0.1: LLC rel inflation=1.0110  trace rel inflation=1.00235  ok=True
d=1000 kappa=  100 h pmax=0.5: LLC rel inflation=1.0620  trace rel inflation=1.02403  ok=True
d=1000 kappa=  100 h pmax=1.0: LLC rel inflation=1.1498  trace rel inflation=1.02671  ok=True
minibatch: LLC-weighted=4636.2127 trace-weighted=1306.5558 ok=True
anti-monotone c: LLC-weighted=4541.3502 trace-weighted=9318.2133 (reversed: True)
```
(The E5 `d = 50`, `κ ≈ 3600`, `lr pmax = 1` row: LLC `+9.4%` against a trace inflation of `0.1%` for a log-uniform spectrum; the note's 44%
reflects its actual Rosenbrock spectrum, which has many stiff directions. The anti-monotone row shows the hypothesis in D is needed.)

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_llc_sensitivity_v1.md`. Summary: A–D correct (finite nonempty spectrum, `pᵢ > 0`, `1 − h pᵢ/2 > 0`); C and D are literally A with `rᵢ = pᵢ` (LLC weights `vᵢ rᵢ`); the minibatch trace formula uses only the diagonal of `UᵀCU`. **Frobenius is genuinely different**: with `gᵢ = 1/(1 − h pᵢ/2) − 1`, the relative Frobenius error is a `1/p²`-weighted RMS of `g` and Chebyshev bounds it only by the *uniform RMS*, not the mean; counterexample `p = (1, 1.1)`, `h = 1.8`: `E_F ≈ 66.9 > 54 = E_LLC`. So the note's E5 Frobenius sentence is *not* a corollary — the theorem is about the trace, and the log says so. `Monovary c̃ p` is sufficient but stronger than needed: the weighted covariance condition `Σᵢⱼ vᵢvⱼ(pᵢ − pⱼ)(c̃ᵢ − c̃ⱼ) ≥ 0` is what the proof uses (and is necessary for `h t² > 0`): expose it, derive the Monovary corollary. Lean: direct double-sum route; trichotomy idiom fine. Extras taken up: the general Laplace-weight comparison (uniform vs `1/p` weights for any comonotone `f`) and the antivary reversal.

## Vote
- Claude: A+B+C+D + the two extras (general Laplace instance, antivary reversal) and the covariance-condition form of A
- GPT-6 Astra: A+B+C+D+extras

Agreed. Proceeding to Step 3.
