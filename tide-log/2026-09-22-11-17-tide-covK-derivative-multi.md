# Tide: covK-derivative-multi

**Direction (user):** Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives.
(Auto-mode continuation: the exact temperature-derivative identity in `d` dimensions, for E2's oscillator.)
**Seabed:** laplace, main 6f2b20a (local; GitHub seabed archived, patch exported)
**Started:** 2026-09-22 (UTC)

## Candidates v1 (Claude)

See `gpt_covK_multi_prompt_v1.md` (A–C verbatim). Working plan: a *general* theorem `hasDerivAt_gibbsExpectation_of_integrable`
(any continuous `L ≥ 0` and `ψ` on `ι → ℝ`, integrability of `ψ e^{−(t/2)L}`, `L ψ e^{−(t/2)L}`, `e^{−(t/2)L}`, `L e^{−(t/2)L}`,
and `Z(t) ≠ 0`), then the separable instances (`uᵢ`, `uᵢuⱼ`, the quadratic probe by linearity and
`gibbsCov_energy_quadratic_split`) and the transport to E2's rotated oscillator.

## Numerical check

`numcheck_covK_multi.py` (`d = 2`, separable, `a = ½`, `λ = (1, 2.5)`, probe `B = [[0.8, −0.3], [−0.3, 1.7]]`, `b = (0.4, −1.1)`):
`Cov_t[L, ψ] = −d⟨ψ⟩/dt` to `7e-11` at `t = 3` and `9e-13` at `t = 10` (quadrature, central differences).

## GPT-6 Astra v1

Verbatim in `gpt_covK_multi_v1.md`. Summary: the DCT is sound (`L ≥ 0` gives `e^{−sL} ≤ e^{−(t/2)L}` on `s > t/2`; `Ioi (t/2)`,
continuity for measurability, `Integrable.norm` for the majorant; nothing new from `volume` on `Fin d → ℝ`); A's arbitrary mixed
monomials would need a new helper (`ℓₖ ∏ uₙ^{eₙ} e^{−aL}`), so prefer direct B with one reusable Gibbs differentiation lemma
instantiated at `1` and the probe; C is straightforward with the transport at every `s` (or eventually near `t`) and the transformed
coefficients `QᵀBQ`, `Qᵀb`. Vote: direct-B+C with a reusable dominated-differentiation helper; defer A.

## Vote
- Claude: general helper + B (coordinates, pairs, quadratic probe by linearity) + C
- GPT-6 Astra: "direct-B+C, with a reusable dominated-differentiation helper; defer A"

Adopted as implemented: `hasDerivAt_gibbsExpectation_of_integrable` is the reusable helper (any continuous `L ≥ 0`); B uses the
seabed's coordinate/pair integrability plus linearity for the probe; A (general monomials) deferred.

## Result

Built locally (`lake build` clean, `scripts/sorries` 0/0/0/0); **not landed** (GitHub seabed archived; patch exported to the SRI,
`staging/pending-patches/tide-64-covK-derivative-multi/`). A general theorem plus B and C landed in the file.
`Laplace/Multi/CovKDerivativeMulti.lean` (     295 lines): `hasDerivAt_integral_mul_exp`, `hasDerivAt_gibbsExpectation_of_integrable` (any continuous `L ≥ 0`),
`gibbsExpectation_finsetSum_of_integrable`, `separableAnharmonic_nonneg`, `partitionFunction_separableAnharmonic_pos`,
`integrable_exp_neg_separableAnharmonic'`, `integrable_energy_separableAnharmonic`, `hasDerivAt_gibbsExpectation_coord`,
`hasDerivAt_gibbsExpectation_coord_mul`, `gibbsExpectation_quadratic_eq`, `hasDerivAt_gibbsExpectation_quadratic`,
`hasDerivAt_gibbsExpectation_rotatedAnharmonic_probe`.

Surprises: the general theorem is the one-dimensional proof verbatim with `ι → ℝ` in place of `ℝ` and the bound
`‖L ψ e^{−(t/2)L}‖` supplied by `Integrable.norm`; the seabed's integrability library covered every instance. Friction:
`norm_nonneg _` and `Integrable.mono'` inside a `refine … ?_` bullet elaborate before the goal's metavariables are known
(pass arguments explicitly), and `gibbsExpectation_add_of_integrable` has *explicit* `L t`.
