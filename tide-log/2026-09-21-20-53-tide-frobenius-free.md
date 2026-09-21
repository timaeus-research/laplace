# Tide: frobenius-free

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"); this tide chosen by the agent: the spectrum-free E4 bound for the covariance (companion of `burnin-envelope`).
**Seabed:** laplace, main after `batch-size-rule` (967d2c8); `GaussianTable.lean` (tide `gaussian-table`)
**Started:** 2026-09-21 (UTC, see filename)

## Context

E4: "The covariance error follows `√(d/(CN))` with a prefactor set by the autocorrelation times." Tide `gaussian-table` proved the spectral
form `frobenius_ula_le`: `E‖Σ̂ − EΣ̂‖_F² ≤ (1/(CN)) ∑ᵢⱼ (1 + δᵢⱼ) s₂ᵢ s₂ⱼ (1 + ρᵢρⱼ)/(1 − ρᵢρⱼ)`, `ρᵢ = 1 − h pᵢ`, `s₂ᵢ = 2h/(1 − ρᵢ²)` the ULA
variances (so `∑ᵢ s₂ᵢ² = ‖Σ_ULA‖_F²`). Tide `llc-variance` stated the isotropic relative bound `(d+1)τ/(CN)`. The general spectrum-free
relative bound — the note's sentence in closed form — is missing.

## Candidates v1 (Claude)

With `r = 1 − h pmin`, `pmin ≤ pᵢ ≤ pmax`, `0 < h pmin`, `h pmax ≤ 1`, `τ(x) = (1 + x)/(1 − x)`:

**A. Algebra.** `tau_lin_mono : 0 ≤ x ≤ x' < 1 → τ(x) ≤ τ(x')`, and the weighted Cauchy–Schwarz step
```
sum_sum_ite_mul_le : 0 ≤ aᵢ → τᵢⱼ ≤ τmax → 0 ≤ τmax →
  ∑ᵢⱼ (1 + δᵢⱼ) aᵢ aⱼ τᵢⱼ ≤ τmax (d + 1) ∑ᵢ aᵢ²
```
(`∑ᵢⱼ aᵢ aⱼ = (∑ a)² ≤ d ∑ a²` by `sq_sum_le_card_mul_sum_sq`, plus the diagonal `∑ a²`).

**B. The spectrum-free covariance bound** (`frobenius_ula_le_free`): on the ULA chain with Gaussian noise,
```
E‖Σ̂ − EΣ̂‖_F² ≤ (d + 1) τ(r²)/(CN) · ∑ᵢ s₂ᵢ²
```
since `ρᵢρⱼ ≤ r²` gives `(1 + ρᵢρⱼ)/(1 − ρᵢρⱼ) ≤ τ(r²)`.

**C. The relative form** (`frobenius_ula_relative_le_free`): `E‖Σ̂ − EΣ̂‖_F² / ‖Σ_ULA‖_F² ≤ (d + 1) τ(r²)/(CN)` — the relative RMS Frobenius
error is at most `√((d+1)τ(r²)/(CN))`, E4's "`√(d/(CN))` with a prefactor set by the autocorrelation times" (`√τ(r²)`, the squared
flattest coordinate's, `≈ √(10κ)` at `h pmax = 0.1`), exact in the isotropic case (`llc_vs_frobenius_isotropic`).

Vote intention: A+B+C.

## Numerical check

`numcheck38.py` (`C = 4`, `N = 10⁴`):
```
d=  10 kappa=100 h pmax=0.2: spectral bound=5.6249e+02  free bound=2.1510e+03  ok=True  relative free = 1.3736e-01  ((d+1)tau/(CN))
d= 100 kappa=100 h pmax=0.2: spectral bound=2.6331e+04  free bound=1.4251e+05  ok=True  relative free = 1.2612e+00  ((d+1)tau/(CN))
d=1000 kappa=100 h pmax=0.2: spectral bound=2.4359e+06  free bound=1.3674e+07  ok=True  relative free = 1.2500e+01  ((d+1)tau/(CN))
d=  10 kappa=  1 h pmax=0.5: spectral bound=8.1481e-03  free bound=8.1481e-03  ok=True  relative free = 4.5833e-04  ((d+1)tau/(CN))
```
The spectrum-free bound dominates the spectral one (by ≈ 4–6 for `κ = 100`) and is tight in the isotropic case.

## GPT-6 Astra v1

Saved verbatim in `tide-log/gpt_frobenius_free_v1.md`. Summary: A–C correct; `τᵢⱼ ≥ 0` is unnecessary (only `aᵢaⱼ ≥ 0`, `τᵢⱼ ≤ τmax`, `τmax ≥ 0`); `τ(y) − τ(x) = 2(y−x)/((1−y)(1−x))`; the relative RMS prefactor against `√(d/(CN))` is `√((d+1)/d · τ(r²))` with `τ(r²) = 10κ − 1/2 + 1/(40κ−2) ≈ 10κ` at `h pmax = 0.1`; "tight isotropically" means the two *bounds* coincide, not equality with the finite-`N` variance; the free/spectral ratio is at most `d` when `pmin` is attained (a separate argument), not in general. The Frobenius identity `∑ s₂ᵢ² = ‖Σ_ULA‖_F²` is immediate mathematically but should be a bridge lemma before the statement is advertised as a matrix-norm result — left as a follow-up; the Lean denominator is `∑ s₂ᵢ²`. Cheap extra taken up: the RMS corollary.

## Vote
- Claude: A+B+C (+ RMS corollary)
- GPT-6 Astra: A+B+C

Agreed. Proceeding to Step 3.
