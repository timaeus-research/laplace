# Tide: mala-invariance

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: the Metropolis-adjusted samplers of the Sanity on Sampling note ("MALA, pMALA: Metropolis-adjusted Langevin, and its version preconditioned by `P^{-1}`; both have the exact stationary law"; conclusion 1: "The Metropolis-corrected MALA lands on `P^{-1}` instead"; E1: "MALA removes the discretisation bias"): the acceptance ratio in closed form, detailed balance, and the invariance of the Gaussian density under the Metropolis-Hastings kernel.
**Seabed:** laplace, commit 8e82906 (branch off main)
**Started:** 2026-09-21-16-12 UTC

## Context

The seabed has the ULA side completely: `ulaCov = (P - (h/2) P^2)^{-1}` is the unique fixed point and `N(0, ulaCov)` is invariant for the ULA
update (`ulaCov_invariant`, `gaussStep`), so the sampled covariance is *not* `P^{-1}`. Nothing about Metropolis corrections exists. The
Gaussian density on `iota -> R` is `gaussianWeight (matCLM P) u = exp(-(1/2) quadForm ...)` (Multi/Defs, GaussianMomentsPosDef); the
ULA update as a random affine map is `ula_update_law` (RandomMap). Mathlib (Sep 2026 pin) has `lintegral_lintegral_swap`/`lintegral_prod`
(Tonelli on `Measure.prod`), `withDensity`, `lintegral_indicator`, `lintegral_add_right_eq_self` (translation invariance of Lebesgue on
`iota -> R`), `ProbabilityTheory.Kernel`.

## Candidates v1 (Claude)

**A. Metropolis–Hastings on `iota -> R`, with the Gaussian target.** Work with unnormalised densities on `iota -> R` with Lebesgue measure.
- A0 (general MH, densities). For measurable `pi, q > 0` with `∫ q(x, y) dy = Z` independent of `x` (`0 < Z < ∞`), set
  `alpha(x,y) = min 1 (pi(y) q(y,x) / (pi(x) q(x,y)))`. Detailed balance holds pointwise:
  `pi(x) q(x,y) alpha(x,y) = min (pi(x) q(x,y)) (pi(y) q(y,x)) = pi(y) q(y,x) alpha(y,x)`. Define the kernel on sets
  `K(x, A) = (1/Z) ∫_A q(x,y) alpha(x,y) dy + (1 - a(x)) 1_A(x)`, `a(x) = (1/Z) ∫ q(x,y) alpha(x,y) dy`. Then for measurable `A`,
  `∫ pi(x) K(x, A) dx = ∫_A pi(x) dx` (Tonelli on the first term, detailed balance, then the rejection term completes `∫_A pi (a + 1 - a)`).
  In Lean: everything as `lintegral` of `ENNReal.ofReal` (no integrability side conditions; Tonelli is `lintegral_lintegral_swap`).
- A1 (the ratio for Gaussian proposals with symmetric drift). For `pi(x) = exp(-(1/2) x^T P x)` and `q(x,y) = exp(-(y - A x)^T S (y - A x))`
  with `S^T = S` and `(S A)^T = S A`: `pi(y) q(y,x)/(pi(x) q(x,y)) = exp(y^T G y - x^T G x)`, `G = S - A^T S A - P/2`. The cross terms
  `x^T S A y` cancel exactly because `S A` is symmetric.
- A2 (MALA). `A = 1 - h P`, `S = 1/(4h)`: `G = -(h/4) P^2`, so the acceptance ratio is `exp(-(h/4)(|P y|^2 - |P x|^2))`; proposals that
  increase `|P x|` are penalised, which is exactly the ULA inflation being removed.
- A3 (pMALA). `A = (1 - h) 1`, `S = P/(4h)`: `G = -(h/4) P`, ratio `exp(-(h/4)(y^T P y - x^T P x))`.
- A4 (the note's claim). Instantiating A0 with A2/A3: the Gaussian density with precision `P` is invariant under the MALA and pMALA kernels
  ("both have the exact stationary law"), in contrast with `ulaCov_invariant`. The normalisation `Z = ∫ exp(-(y - Ax)^T S (y - Ax)) dy` is
  independent of `x` by translation invariance (no need to compute it), and `0 < Z < ∞` for `S` positive definite.

**B (optional).** Identify `volume.withDensity (ofReal ∘ pi)`, normalised, with `multivariateGaussian 0 P^{-1}` if Mathlib exposes the
density of `multivariateGaussian` (unclear); otherwise state A4 at the density level and record the identification as a follow-up.

**C (out of scope).** Geometric ergodicity / convergence of the MALA chain law.

## Numerical check

`numcheck22.py` (`d = 3`, random PD `P`, `h = 0.3/p_max`): the direct MH log-ratio `log pi(y) + log q(y,x) - log pi(x) - log q(x,y)` agrees
with `-(h/4)(|Py|^2 - |Px|^2)` (MALA) and `-(h/4)(y^T P y - x^T P x)` (pMALA) to `2e-14` at random points, and with the general form
`y^T G y - x^T G x`, `G = S - A^T S A - P/2`; `SA` is symmetric in both cases. Long runs (400k steps, 10% burn-in) give sample covariances
within `1.1%` (MALA, acceptance 0.96) and `1.2%` (pMALA, acceptance 0.99) of `P^{-1}` in Frobenius norm, while the ULA law
`(P - (h/2) P^2)^{-1}` is `2.8%` away from `P^{-1}`.

## GPT-6 Astra v1

Saved verbatim in `gpt_mala_invariance_v1.md`. Summary: A0–A4 correct; A1 needs only `S^T = S` and `(SA)^T = SA` (not `P` symmetric);
the invariance proof is complete with joint measurability of `q`, finite positive `pi, q`, and a common row integral `Z in (0, ∞)`;
Tonelli on nonnegative integrands needs no integrability; "invariant probability law" additionally needs `0 < ∫ pi < ∞` (true for PD
`P`); no ULA stability restriction is needed (every `h > 0`). Lean: separate the flux `F(x,y) = ofReal(min(pi q, pi' q'))` (symmetric,
jointly measurable, `= ofReal(pi x) w(x,y)`) and swap *that*; prove `a(x) <= 1` before any ENNReal subtraction; combine accepted and
rejected integrands as `pi(y)(a(y) + (1 - a(y)))`; keep the conventional `alpha` and prove the minimum-flux lemma once over `R`; pass `Z`
with the hypothesis `∀ x, ∫ q(x,·) = Z`; the Gaussian functions are continuous so `.measurable` suffices; do not plan B around an
assumed `multivariateGaussian` density lemma — the normalised density-level statement is a complete endpoint, and covariance `P^{-1}` as
a moment statement is a separate result. Suggested order: flux lemma, setwise invariance, kernel packaging, general ratio, MALA/pMALA,
normalised Gaussian invariance. **Vote: A** (with joint measurability, `0 < Z < ∞`, `P` PD, `h > 0`, target normalisation; kernel
packaging and reversibility if cheap; B opportunistic).

## Vote
- Claude: candidate A (A0–A4 plus the normalised-law invariance; kernel packaging and reversibility deferred)
- GPT-6 Astra: candidate A

Agreed.
