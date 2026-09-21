# Tide: mala-kernel

**Direction (user):** auto mode ("Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives"; "Continue with what you think best, don't stop"). Chosen: finish the Metropolis arc of the Sanity on Sampling note begun in `mala-invariance`: package the Metropolis–Hastings kernel as a `ProbabilityTheory.Kernel`, prove it is Markov and that the Gaussian law is a fixed point of `Measure.bind` ("both have the exact stationary law"), and identify the invariant law's moments: mean `0`, covariance `P^{-1}` ("MALA lands on `P^{-1}`").
**Seabed:** laplace, commit 0f91e5c (branch tide/mala-invariance, chained)
**Started:** 2026-09-21-16-40 UTC

## Context

`mala-invariance` proved, at the level of set functions and `lintegral`s: `mhKernelSet pi q mu Z x E = Z^{-1} ∫_E q alpha + (1 - a x) 1_E(x)`,
`mh_invariant : ∫ pi(x) K(x,E) dx = ∫_E pi`, `mh_invariant_law : ∫ K(x,E) d nu = nu(E)` for `nu = mhTargetLaw pi mu T = mu.withDensity (ofReal pi / T)`,
`isProbabilityMeasure_mhTargetLaw`, `measurable_mhKernelSet`, `mhAcceptMass_le_one`; for the Gaussian target `targetWeight P x = exp(-x^T P x/2)`,
`gaussianLaw P = mhTargetLaw (targetWeight P) volume (targetZ P)`, `mala_invariant_law`, `pmala_invariant_law`. The seabed also has the tilted
Gaussian moments on `iota -> R`: `tiltedExpectation P v phi = (∫ phi u * tiltedWeight P v u)/tiltedZ P v`, `tiltedExpectation_coord_mul hP v i j =
P^{-1} i j + m_i m_j`, `tiltedExpectation_coord = tiltMean`, `tiltedWeight_zero : tiltedWeight P 0 = gaussianWeight (matCLM P)`, `tiltMean P 0 = 0`.
Mathlib: `Kernel` (a measurable `X -> Measure X`; `Measure.measurable_of_measurable_coe`), `IsMarkovKernel`, `Measure.bind_apply hE (hf : AEMeasurable f)`,
`Measure.dirac_apply'`, `withDensity_apply`, `integral_withDensity_eq_integral_smul` (NNReal density) / `…_toReal_smul`,
`integral_eq_lintegral_of_nonneg_ae`.

## Candidates v1 (Claude)

**A (main). The MH kernel as a Markov kernel and the fixed-point statement.**
- A1. `mhKernel pi q mu Z : Kernel X X` with `mhKernel x = mu.withDensity (fun y => ofReal (q x y alpha(x,y))/Z) + (1 - a x) • dirac x`;
  `mhKernel_apply : mhKernel x E = mhKernelSet pi q mu Z x E` for measurable `E`; measurability of the kernel from `measurable_mhKernelSet`.
- A2. `IsMarkovKernel (mhKernel …)` under the standing hypotheses (`0 < Z < ∞`, `q > 0`): `K x univ = a x + (1 - a x) = 1`.
- A3. `(mhTargetLaw pi mu T).bind (mhKernel …) = mhTargetLaw pi mu T` (Measure.ext on measurable sets + `bind_apply` + `mh_invariant_law`).
- A4. Gaussian instances: `malaKernel P h`, `pmalaKernel P h : Kernel (iota -> R) (iota -> R)`, Markov, and `(gaussianLaw P).bind (malaKernel P h) = gaussianLaw P`
  for every `h > 0` (`P` PD for pMALA's proposal).

**B. The moments of the invariant law**: `∫ x, x i ∂(gaussianLaw P) = 0` and `∫ x, x i * x j ∂(gaussianLaw P) = P^{-1} i j` for `P` PD, by bridging
`gaussianLaw P` (ENNReal density `ofReal(targetWeight P)/targetZ P`) to the seabed's real `tiltedExpectation P 0`: `targetWeight P = tiltedWeight P 0`,
`(targetZ P).toReal = tiltedZ P 0` via `integral_eq_lintegral_of_nonneg_ae`, and `integral_withDensity_eq_integral_toReal_smul`. This is the
"covariance `P^{-1}`" moment statement GPT-6 Astra asked for, separate from the density-level invariance.

**C (optional).** Reversibility: `∫_E K(x, F) d nu = ∫_F K(x, E) d nu` from the symmetric flux — a corollary of the same Tonelli argument.

Proposed: A + B (+ C if cheap), one module `Laplace/Sampler/MetropolisKernel.lean` (~300 lines).

## Numerical check

Structural: the kernel identities (`K(x, E) = Z^{-1} ∫_E q alpha + (1 - a(x)) 1_E(x)`, `K(x, univ) = 1`) are algebraic consequences of the
`mala-invariance` definitions, and the moment statements are exact Gaussian integrals. The Monte Carlo of `numcheck22.py` already checks the
substance: 400k MALA/pMALA steps give sample covariances within `1.1%`/`1.2%` of `P^{-1}`, with acceptance 0.96/0.99.

## GPT-6 Astra v1

Saved verbatim in `gpt_mala_kernel_v1.md`. Summary: A1–A4 and B correct; the measure-level definition
`mu.withDensity (ofReal(q alpha)/Z) + (1 - a x) • dirac x` is right with ENNReal truncated subtraction, and
`Measure.measurable_of_measurable_coe` (measurability of `x ↦ K x E` for every measurable `E`) suffices to build the `Kernel`; prove the
raw-measure application lemma first, then use it in the constructor; a `Kernel` cannot omit the hypotheses its measurability field needs,
so carry them as arguments; prefer `Measure.withDensity` over `Kernel.withDensity`. Markovness needs the full standing hypotheses (row
normalisation with `Z`, `0 < Z < ∞`, `q > 0`), not just two of them. State the fixed point literally as `Measure.bind ν K = ν` by
`Measure.ext`; `bind_apply` needs only measurability of `E` and a.e.-measurability of the kernel (no `SFinite`). For the moments use
`integral_withDensity_eq_integral_toReal_smul`, `ENNReal.toReal_div`, `toReal_ofReal`, and `integral_eq_lintegral_of_nonneg_ae` for the
normaliser; export the integrability facts (from `integrable_coord_mul_gaussianWeight_matCLM`) so that "mean" and "covariance" are
genuine, and add the centred corollary; positive definiteness of `P` for both Gaussian stationary-law specialisations. Iterated
stationarity by induction is cheap; C (reversibility) is correct but not cheap — defer. **Vote: A+B.**

## Vote
- Claude: A+B (with integrability, the centred covariance corollary and `n`-step stationarity; C deferred)
- GPT-6 Astra: A+B

Agreed.
