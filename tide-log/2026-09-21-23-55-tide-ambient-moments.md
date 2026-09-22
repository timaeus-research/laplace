# Tide: ambient-moments

**Direction (user):** auto mode on the Sanity-on-Sampling note; the ambient mean vector and covariance matrix of the note's rotated anharmonic
potential (bilinearity of Gibbs moments under integrability, integrability transport through the frame change, `Cov_w = Q diag(Var) Qᵀ`),
and E2's first panel in Frobenius form: the relative Frobenius error of the Laplace covariance prediction is `|a² − ½|/t + o(1/t)`.
**Seabed:** laplace, commit 2d8170f (main, after tide `gibbs-rotation`)
**Started:** 2026-09-21T23:56Z

## Candidates v1 (Claude)

See `gpt_ambient_moments_prompt_v1.md` (A–D verbatim).

- A: bilinearity of `gibbsExpectation`/`gibbsCov` under integrability of the weighted integrands.
- B: integrability of the rotated coordinates and their products against the rotated Boltzmann factor, by change of variables.
- C: `⟨wⱼ⟩ − cⱼ = ∑ᵢ Qⱼᵢ ⟨uᵢ⟩`, `Cov_w[wⱼ, wₖ] = ∑ᵢ Qⱼᵢ Qₖᵢ Var_{ℓᵢ}` and the ambient mean asymptotics.
- D: `t² ‖Cov_w − S_w‖_F²/‖S_w‖_F² → (a² − ½)²`: the relative Frobenius error of the Laplace covariance is `|a² − ½|/t + o(1/t)`.

## GPT-6 Astra v1

Saved verbatim in `gpt_ambient_moments_v1.md`. Summary: A–D correct with explicit normalisation/nondegeneracy hypotheses; finite-sum linearity
needs integrability, scalar multiples do not, and the constant/translation identities of C need `⟨1⟩ = 1` from `Z ≠ 0` (add lemmas for the
expectation of a constant and covariance invariance under adding constants). B: use exponent vectors `e = 1_{k=i} + 1_{k=j}` so the diagonal
case gives degree two; route (i) (matrix lemma + translation) is the least painful, check the orientation of `comp_sub_right`. C is affine
reconstruction + bilinearity + frame independence + diagonal separable covariance. D: with `rᵢ = λᵢtVᵢ − 1`, `W = ∑ λᵢ⁻²`,
`R² = ∑ λᵢ⁻² rᵢ²/W`, so `t²R² → b²` and `tR → |b|`, valid at `b = 0` too; **the universality comes from the common directional coefficient,
not from rotation alone** (with direction-dependent `bᵢ` the limit would be the `λ⁻²`-weighted RMS of the `bᵢ`); the theorem does not certify the
finite-`t` value at `t = 10`; make the squared-ratio `Tendsto` primary; the note normalises by the prediction (normalising by the exact
covariance has the same leading coefficient); do not bring `Σ_ULA` in. Vote: A–D.

## Vote
- Claude: A+B+C+D
- GPT-6 Astra: A+B+C+D

## Numerical check

`numcheck_ambient_moments.py` (`d = 4`, `λ = (1, 2, 5, 10)`, `a = ½`): `t · ‖Cov − S‖_F/‖S‖_F = 0.2655, 0.2526, 0.2503` at `t = 10, 100, 1000`
(→ 0.25, spectrum-independent); identical in a random frame `Q`; `t(⟨w⟩ − c) = Q(t⟨u⟩)` to 1e-14 and within 1% of `−Q(αᵢ/(2λᵢ²))` at `t = 100`.
