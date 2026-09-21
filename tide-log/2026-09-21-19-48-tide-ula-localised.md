# Tide: ula-localised

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the ULA-corrected localised LLC (E3).
**Seabed:** laplace, main after `localised-llc-bounds` (c7b4503)
**Started:** 2026-09-21 (UTC, see filename)

## Context

E3 of the sanity note: "The LLC shrinks as `½ t tr(H(tH + γI)⁻¹)`: measured 4.23, 2.55, 0.83 against predicted 4.20, 2.50, 0.80 at
`γ_rel = 1, 10, 100`; the residual is the 5% ULA inflation of the stiff directions at `lr pmax = 0.1`." Its left panel plots the trace of the
sampled covariance against the trace of `(tH + γI)⁻¹` "and of its ULA-corrected form (hollow)". The seabed has the ULA law `Σ_ULA = ulaCov P h
= (P − (h/2)P²)⁻¹` for any precision `P`, its trace in `P`'s eigenvalues (`trace_mul_ulaCov`, `ula_llc`, γ = 0), and, from tide
`localised-llc-bounds`, the conjugation of `tH + γI` and of its inverse into the eigenbasis `U = orthoOf hH.1` of `H`
(`orthoOf_transpose_localised_mul`, `orthoOf_transpose_localised_inv_mul`) with the eigen form `localisedLLC hH t γ = ½ ∑ᵢ tλᵢ/(tλᵢ + γ)`.
What is missing is the ULA law *for the localised precision* expressed in `H`'s eigenvalues (Mathlib's eigenvalues of `tH + γI` are not
syntactically `tλᵢ + γ`), and the comparison with the exact localised LLC.

## Candidates v1 (Claude)

Let `H` be positive definite with eigenvalues `λᵢ`, `t > 0`, `γ ≥ 0`, `aᵢ = tλᵢ + γ` the eigenvalues of `P = tH + γI`, `0 < h`, `h aᵢ < 2`.

**A. The ULA covariance of the localised precision in `H`'s eigenbasis.**
```
orthoOf_transpose_ulaDenom_mul : Uᵀ (P − (h/2)P²) U = diag(aᵢ − (h/2)aᵢ²)
orthoOf_transpose_ulaCov_localised_mul : Uᵀ (ulaCov P h) U = diag(1/(aᵢ(1 − h aᵢ/2)))
trace_ulaCov_localised : tr(ulaCov P h) = ∑ᵢ 1/(aᵢ(1 − h aᵢ/2))          (E3 left panel, "ULA-corrected form")
```

**B. The ULA-corrected localised LLC.**
```
ula_localised_llc : (t/2) tr(H · ulaCov P h) = ½ ∑ᵢ (tλᵢ/(tλᵢ + γ)) / (1 − h(tλᵢ + γ)/2)
```
(the `γ = 0` case is `ula_llc`; the `h → 0` value is `localisedLLC hH t γ`).

**C. The ULA inflation of the localised LLC.** With `aᵢ ≤ pmax` and `h pmax < 2`:
```
localisedLLC_le_ula_localised : localisedLLC hH t γ ≤ (t/2) tr(H · ulaCov P h)
ula_localised_llc_le          : (t/2) tr(H · ulaCov P h) ≤ localisedLLC hH t γ / (1 − h pmax/2)
```
so at `h pmax = 1/10` the ULA-corrected localised LLC exceeds the exact one by at most the factor `20/19 ≈ 1.053` — the note's "5% ULA
inflation" (the exact excess on each direction is `(h aᵢ/2)/(1 − h aᵢ/2)`, largest on the stiff directions).

Vote intention: A+B+C.

## Numerical check

`numcheck33.py`, E3 setting (`d = 10`, log-uniform spectrum with `κ = 100`, `t = 100`, `h pmax = 0.1` with `pmax = tλ_max + γ`), the matrix
form `(t/2) tr(H (P − (h/2)P²)⁻¹)` in a random orthogonal frame against the eigen sum:
```
gamma_rel=   1: ULA-corrected LLC matrix=4.2633 eigen=4.2633 | exact localised=4.1998 | ratio=1.0151 (bound 1/(1-h pmax/2)=1.0526) | tr: 1.60542 vs 1.60542
gamma_rel=  10: ULA-corrected LLC matrix=2.5584 eigen=2.5584 | exact localised=2.5000 | ratio=1.0233 (bound 1/(1-h pmax/2)=1.0526) | tr: 0.50462 vs 0.50462
gamma_rel= 100: ULA-corrected LLC matrix=0.8325 eigen=0.8325 | exact localised=0.8002 | ratio=1.0404 (bound 1/(1-h pmax/2)=1.0526) | tr: 0.08658 vs 0.08658
note measured: 4.23, 2.55, 0.83
```
The ULA-corrected localised LLC reproduces the note's *measured* values (4.23, 2.55, 0.83) to within 1%, better than the exact localised
values (4.20, 2.50, 0.80): the E3 residual is indeed the ULA inflation, and it sits inside the `1/(1 − h pmax/2)` bound.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_ula_localised_v1.md`. Summary: A–C correct; stability is `0 < h aᵢ < 2`, i.e. `h(tλ_max + γ) < 2` — localisation tightens the step constraint; B's `γ = 0` case is the unlocalised formula for the precision `tH` and `h → 0` gives `localisedLLC`; the per-direction relative excess `(h aᵢ/2)/(1 − h aᵢ/2)` is strictly increasing in `aᵢ`, so at `h pmax = 0.1` the maximum is `1/19 ≈ 5.26%` (not exactly 5%); the E3 reading (localisation pushes all `aᵢ/pmax` towards 1, so the inflation grows with `γ`) is right, and the predicted excesses 1.5/2.3/4.0% against the measured 0.7/2.0/3.7% *support*, not prove, the attribution of the residual to ULA bias. Lean: direct conjugation + explicit inverse (as in tide 30), a reusable product-conjugation step with `U Uᵀ = 1`, `diagonal_sub` backwards to combine; keep `(h/2) • (P * P)` explicit. Cheap addition taken up: the trace ratio `1 ≤ tr Σ_ULA / tr P⁻¹ ≤ 1/(1 − h pmax/2)` (E3 left panel); the `λ_max` form of the stability iff left aside.

## Vote
- Claude: A+B+C (+ the trace-ratio corollary)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.
