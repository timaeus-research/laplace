# Tide: sanity-closed-forms

**Direction (user):** "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." Continuing the programme of the sampler-laws tide: formalise the mathematics used in the Sanity on Sampling note (learning-theory/papers/sanity/main.tex, project sanity) in the laplace seabed. This tide takes the remaining *closed-form reference values* of the note: the exact Gibbs moments of the two-dimensional Rosenbrock potential (E5, E7 reference), the expected pooled sample variance of a finite AR(1) chain started at the mode (the note's "finite-chain prediction", E1/E2/E4), and the ULA-corrected LLC trace formula.
**Seabed:** laplace, commit ee83216 (origin/main at tide start; the sampler-laws tide landed at f760ed6)
**Started:** 2026-09-21T04:36Z
**Worktree / branch:** learning-theory/lean/laplace-tide-sanity-closed-forms, tide/sanity-closed-forms
**Retrospective:** skipped by user instruction for this auto run ("don't worry about retrospectives"); the tide log carries the Result section.

## Seabed snapshot

- Sampler arc from the previous tide: `Laplace/Sampler/Lyapunov.lean`, `Laplace/Sampler/ULA.lean`, `Laplace/Multi/GaussianLLC.lean` (see `tide-log/2026-09-21-01-57-tide-sampler-laws.md`).
- 2D track on `ℝ × ℝ` (`Laplace/TwoD/`): additively separable potentials only (`AddSeparable.lean`, `PureQuartic.lean`, `SemiDegenerate.lean`, `QuarticSextic*.lean`), factorisation through `MeasureTheory.integral_prod_mul`. No non-separable 2D potential yet.
- 1D Gaussian moments `Laplace/OneD/GaussianMoments.lean` (`integral_pow_mul_exp_neg_t_sq_half`, odd moments vanish), harmonic Gibbs expectations `Laplace/OneD/Harmonic.lean`.
- Nothing on stochastic processes / AR(1) beyond the scalar `ar1_var_iterate`.

## Candidates v1 (Claude)

Verbatim in `tide-log/gpt_sanity_closed_forms_prompt_v1.md`. In brief: **A** exact Gibbs moments of the 2D Rosenbrock potential `L = (a(y-x²)² + (1-x)²)/2` (shear/Fubini structural lemma, Z, first and second moments, `E[L] = 1/t`, exact covariance minus Laplace covariance `= (2/t²) e_y e_yᵀ`); **B** finite AR(1) chain started at the mode in an inner-product space: second-moment table `⟪x_k, x_l⟫ = σ²(ρ^|k-l| - ρ^{k+l})`, window sums, expected pooled sample variance over C chains (the note's `ar1_expected_sample_variance`); **C** `trace(P · ulaCov P h) = Σ 1/(1 - h p_i/2)` (ULA-corrected LLC).

## Numerical check

scipy `dblquad` at a = 100, t = 7 against the closed forms of A: Z 0.0897597899 vs 2π/(t√a) 0.0897597901; E[x] = 1.0000000; E[y] 1.14285713 vs 1 + 1/t; Var x 0.142857132 vs 1/7; Cov 0.285714265 vs 2/7; Var y 0.61367337 vs 4/t + 2/t² + 1/(ta) = 0.61367347; E[xy] 1.4285714 vs 1 + 3/t; E[y²] 1.91979580 vs 1.91979592; t⟨K⟩ = 0.99999996. Laplace S = (tH)⁻¹ with det H = 100; stiff-eigendirection ratio exact/Laplace = 1 + 199.68/t (the note's "1 + 200/t").
B: Monte Carlo (4·10⁵ chains, ρ = 0.9, v = 1, N = 12, b = 5, C = 3): pooled expected sample variance 3.6332 ± 0.0035 vs closed form 3.6362; second-moment table `σ²(ρ^|k-l| - ρ^{k+l})` matches E[x_k x_l] to 0.014 (MC standard error 0.008); the Toeplitz double-sum identity checked exactly (3.0809507 both sides).
C: algebraic consequence of `ulaCov_conj_apply`; no separate check.

## GPT-6 Astra v1

Verbatim in `tide-log/gpt_sanity_closed_forms_v1.md`. Summary:
- A correct, including `Cov - (tH)⁻¹ = (2/t²) e_y e_yᵀ` (about the Gibbs mean; about the mode the second moment differs by `3/t²` instead); the stiff-direction ratio is `1 + 2λ₊(q₊)_y²/t ≈ 1 + 199.4/t`, an approximation to keep as commentary. Cheap follow-on: `E[L²] = 2/t²`, `Var L = 1/t²`.
- B correct with `N > 0`, `C > 0`; divisor `CN` (not Bessel). Organise as Gram identity → orthogonal-chain pooling → AR(1) Gram table → Toeplitz sum. Label as a second-moment theorem until the L² bridge exists.
- C correct; the "100 at h p_max = 1.9" quote holds only for an isotropic spectrum (in general `≤`). Suggested follow-on: `LLC_ULA - d/2 = ½ Σ (hp_i/2)/(1 - hp_i/2)` and `d/2 ≤ LLC_ULA ≤ d/(2(1 - hp_max/2))`.
- Route for A: one reusable measure-preserving triangular shear (Tonelli + translation invariance, or an existing skew-product lemma), fully centred `T(z,u) = (1+z, u+(1+z)²)`, transported weight `G_t(z) G_{ta}(u)`; a universal integrability lemma for `p.1^m p.2^n · weight` proved via transported monomials and `Integrable.mul_prod`; explicit transported polynomial identities by `ring`.
- Better abstraction: the curved Gaussian valley `L_g = ((x-μ)² + a(y-g(x))²)/2` with `Z_g = 2π/(t√a)` for any measurable `g`.
- Vote: **A0–A5 alone** (Rosenbrock exact moments + covariance/Laplace discrepancy on a reusable shear lemma); B and C as separate excursions.

## Integration (Claude)

Accepted. This tide takes A in the general-valley form: the measure-preserving shear for a continuous `g`, the partition function `Z_g = Z_harm(1) Z_harm(a)` for any continuous `g`, transport of integrals and integrability, and for Rosenbrock (`μ = 1`, `g x = x²`) the raw moments, covariance matrix, `E[L] = 1/t`, `Var L = 1/t²`, plus the Laplace comparison stated through the polynomial identity `L(1+z, 1+w) = ½ (z,w) H (z,w)ᵀ - a(w - 2z) z² + a z⁴/2` (certifying `H = [[1+4a, -2a],[-2a, a]]` as the Hessian at the minimiser without derivatives) and `Cov - (tH)⁻¹ = (2/t²) e_y e_yᵀ`. Transported moments are products of the seabed's 1D harmonic Gibbs expectations (`gibbsExpectation_harmonic_pow_even/odd`), which avoids rpow algebra. B and C (with GPT's ULA-trace bounds) go to the next tide, already deliberated here.

## Vote
- Claude: A (general shear + Rosenbrock exact moments + Laplace comparison).
- GPT-6 Astra: A0–A5 alone.

Agreed after one round.
