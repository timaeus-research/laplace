# Tide: sampler-gamma-law

**Direction (user):** auto mode — "Just proceed on auto. You can bite off big chunks here to formalise and don't worry about retrospectives." / "Continue with what you think best, don't stop". Claude's choice for tide 91: the sampler-side transfer GPT repeatedly suggested — the Gamma law of the LLC statistic under the Gaussian laws of the sampler files (exact Gibbs target, localised target, ULA stationary law), where the Laplace transform is exact.
**Seabed:** laplace, commit 1745924 (tide 90 landed)
**Started:** 2026-09-23T01:16Z

## Seabed (sampler side, Gaussian)
`tiltedExpectation P v φ := (∫ φ u · exp(−½uᵀPu + vᵀu)) / tiltedZ P v` on `ι → ℝ` (finite `ι`), `tiltedWeight P 0 u = gaussianWeight (matCLM P) u
= exp(−½ uᵀPu)`, `gaussianZ_matCLM (hP : P.PosDef) : gaussianZ (matCLM P) = √(2π)^{card ι} · (√det P)⁻¹`, `effectivePrecision_posDef :
(t•H + γ•1).PosDef` for `H.PosDef`, `t > 0`, `γ ≥ 0`; `localised_llc_centred : t · tiltedExpectation (t•H + γ•1) 0 (½uᵀHu) = ½∑ᵢ tλᵢ/(tλᵢ+γ)`
(E3/E6); eigenbasis `U = orthoOf hH` (orthogonal, `Uᵀ(t•H + γ•1)U = diagonal (tλᵢ + γ)`, `orthoOf_transpose_localised_mul`;
`Uᵀ(P_γ − (h/2)P_γ²)U = diagonal(aᵢ(1 − haᵢ/2))`, `aᵢ = tλᵢ + γ`, `orthoOf_transpose_ulaDenom_mul`); the ULA stationary law `N(0, Σ_ULA)`,
`Σ_ULA = (P − (h/2)P²)⁻¹` (`ulaCov`, `ulaCov_invariant` via Mathlib's `multivariateGaussian`), `ula_llc = ½∑ 1/(1 − hpᵢ/2)`, `pᵢ = tλᵢ`
(`llc_ula_invariant`), the ULA-corrected localised LLC `½∑(tλᵢ/(tλᵢ+γ))/(1 − h(tλᵢ+γ)/2)` (`ula_localised_llc`).

## Candidates v1 (Claude)

**A1 (exact, general).** For `Q.PosDef`, `H` symmetric and `(Q + s•t•H).PosDef`:
**`tiltedExpectation Q 0 (fun u => exp(−s·t·½uᵀHu)) = √(det Q) / √(det(Q + s•t•H))`** — the integrand identity
`exp(−s t ½uᵀHu)·exp(−½uᵀQu) = exp(−½uᵀ(Q + stH)u)` and `gaussianZ_matCLM` twice (the `√(2π)^d` cancels). No commutation needed.

**A2 (exact Gibbs law, E3's target).** `Q = t•H + γ•1`, `s > −1`: **`= ∏ᵢ (1 + s·tλᵢ/(tλᵢ + γ))^{−1/2}`** (determinants in the
eigenbasis: `det(Uᵀ A U) = det A`, `det diagonal = ∏`); at `γ = 0`: **`= (1+s)^{−d/2}` exactly for every `t`** — under the Gaussian Gibbs
law the LLC statistic `t·½wᵀHw` is exactly `Gamma(d/2, 1)` (tide 89's limit law is exact when the anharmonic corrections vanish); for
`γ > 0` it is a sum of independent `Gamma(½, rate (tλᵢ+γ)/(tλᵢ))`, whose mean is E3/E6's localised LLC `½∑tλᵢ/(tλᵢ+γ)`.

**A3 (the ULA law).** `Q = P − (h/2)P²` with `P = t•H`, `0 < hpᵢ < 2`, `s ≥ 0` (or `s > −(1 − hp_max/2)`):
**`= ∏ᵢ (1 + s/(1 − hpᵢ/2))^{−1/2}`** — under the ULA stationary law the sampled LLC statistic is a sum of independent
`Gamma(½, rate 1 − hpᵢ/2)`: the "ULA inflation" of `ula_llc` (mean `½∑1/(1 − hpᵢ/2)`) is a per-direction Gamma *rate* shift, not a
shape change; combined localised ULA law `Q = P_γ − (h/2)P_γ²`: `∏ᵢ (1 + s·tλᵢ/(aᵢ(1 − haᵢ/2)))^{−1/2}`, mean `ula_localised_llc`.
(We would state A3 with the seabed's `tiltedExpectation (P − (h/2)P²) 0`, i.e. the Gaussian law with covariance `Σ_ULA`, and cite the
sampler files' identification of `N(0, Σ_ULA)` as the ULA invariant law in prose — unless a bridge lemma `tiltedExpectation Σ⁻¹ 0 φ =
∫ φ d(multivariateGaussian 0 Σ)` is cheap; is it? Mathlib defines `multivariateGaussian μ S = stdGaussian.map (x ↦ μ + √S x)` with
`CFC.sqrt`, and has `charFun_multivariateGaussian` but no density lemma.)

**B (comparison with E2).** Wording: the anharmonic localised energy's transform (tide 89–90) equals the Gaussian one (A2) up to the
`O(1/t)` correction `−s(∑e₁ᵢ)/((1+s)^{d/2+1}t)`; the ULA law adds the rate shifts `1 − hpᵢ/2`. Two independent finite-`t` corrections to
the Gamma law of `tK`: anharmonicity (`E/t`) and discretisation (`h`). Not a theorem, a remark for §14/E3.

## Numerical check (d = 3 random PosDef H, t = 2, γ = 0.7, h = 0.15, Monte Carlo 2·10⁶ samples)
All four laws: MC vs determinant vs product formulas agree to the MC error (e.g. ULA law, s = 1: `0.24490 ± 0.00018` vs `0.24511`;
Gibbs γ = 0, s = 3: `0.12496 ± 0.00014` vs `(1+3)^{−3/2} = 0.125`).

## Questions put to GPT-6 Astra
1. Are A1–A3 correct, including the domains of `s` (A2: `s > −1`; A3: `s ≥ 0` suffices for the Gamma identification — is the natural
   MGF domain `s > −(1 − hp_max/2)`?) and the Gamma identifications (sum of independent `Gamma(½, rate rᵢ)` has transform
   `∏(1 + s/rᵢ)^{−1/2}`)?
2. Bundle and route: A1 via `gaussianZ_matCLM` twice, eigenbasis determinants via `det_mul`/`det_transpose`/`det_diagonal` and
   `Uᵀ U = 1`; PosDef of `Q + s•t•H` for A3 (`U diag(pᵢ(1 − hpᵢ/2) + s pᵢ) Uᵀ`) — is there a slicker PosDef argument than eigenvalue
   positivity (e.g. `Q + s P = P(1 + s − (h/2)P)` as a product of commuting PosDef matrices)? Anything in A1's integrand identity that
   needs care (`quadForm (matCLM (Q + s•t•H)) u = quadForm Q u + s t quadForm H u` via `mulVec_add`, `dotProduct_add`)?
3. Anything missed close to this seabed: e.g. the *cumulants* of the sampled LLC statistic from the exact transform (`κₙ = (n−1)!·½∑rᵢ^{−n}`)
   — worth stating the variance `½∑(1 − hpᵢ/2)^{−2}` as the ULA-inflated version of tide 85's `d/2`? Is the minibatch law
   (`Sampler/Minibatch.lean`, stationary covariance with `(1 + ht²C̃ᵢᵢ/2)` factors) also a product of Gammas (only if `C̃` is diagonal in
   `U`)? Is there value in the finite-time (non-stationary, `Σ_k` from the mode) transform `√(det Q_k)/…`?
4. Wording against E3 ("the LLC shrinks as ½ t tr(H(tH+γI)⁻¹)", "5% ULA inflation of the stiff directions"): is "under the sampler's
   stationary law the LLC statistic is a sum of independent Gammas whose rates carry the localisation and the discretisation" a fair
   gloss; what qualifications (Gaussian target only; stationary law, not the finite-chain average; `hpᵢ < 2`; the identification of the
   Gibbs-formalism law with Mathlib's `N(0, Σ_ULA)` cited, not re-proved)?
Vote for one bundle at the end.

(The numerical check script is `numcheck_sampler_gamma_law.py` in this directory; full output in the tide's SRI note.)

## GPT-6 Astra v1

Verbatim in `gpt_sampler_gamma_law_v1.md`. Summary: A1–A3 correct; A1 needs no commutation and no sign of `s`, only positive
definiteness of the modified precision `Q + stH` (which makes the numerator integrable even for `s < 0`); A2's maximal domain is
`s > −minᵢ(1 + γ/pᵢ)` (larger than `s > −1` when `γ > 0`); A3's Laplace domain `s > −(1 − hp_max/2)` (MGF parameter `z < 1 − hp_max/2`),
`s ≥ 0` entirely reasonable for the formal theorem; `d = 0` is `δ₀`, not a positive-shape Gamma. Route: pointwise weighted-integrand
identity → expectation as `tiltedZ(Q + stH, 0)/tiltedZ(Q, 0)` → `gaussianZ_matCLM` twice → cancel `√(2π)^d` (record `det > 0`, square
roots `≠ 0`); `det(UᵀAU) = det A` from `det(UᵀU) = 1` (no sign split); prefer `∏ᵢ (√(1 + s/rᵢ))⁻¹` over real powers; PosDef of `Q + sP`
for `s ≥ 0` via `Q ≻ 0`, `sP ⪰ 0`; eigenvalue positivity for negative `s`. The `multivariateGaussian` bridge is *not* cheap (no density
lemma): prove A3 for `tiltedExpectation Q 0` and say the bridge is not machine-checked. Cumulants `κₙ = (n−1)!/2 · ∑rᵢ⁻ⁿ`, variance
`½∑(1 − hpᵢ/2)⁻²` (discretisation inflates the variance more than the mean) — remark only (differentiating the transform is not free).
Minibatch: a covariance formula does not imply a Gaussian stationary law; with Gaussianity, diagonalise `tΣ^{1/2}HΣ^{1/2}`. Finite time:
covariance-side `det(I + stΣ_k^{1/2}HΣ_k^{1/2})^{−1/2}`, deferred. Wording: "for the centred Gaussian target, under the stable ULA
stationary Gaussian law, the scaled quadratic energy is a sum of independent shape-½ Gammas; localisation and discretisation modify
their rates"; qualifications: the LLC estimate is the *mean* of this statistic (not the finite-chain average's law), stability
`h(tλᵢ + γ) < 2`, "5% inflation" is the exact multiplier `(1 − haᵢ/2)⁻¹ ≈ 1.05`, the discretisation parameter is `hpᵢ = htλᵢ` (fixed
`h` is not stable as `t → ∞`; the uninflated limit needs `h(t)t → 0`); before comparing tide 90's anharmonic correction *relative to A2*
note that A2 itself carries a `1/t` localisation correction at fixed `γ`.

## Vote
- Claude: A1 + A2 + localised-ULA product for `s ≥ 0` (unlocalised A3 as a specialisation); Gamma interpretation in prose
- GPT-6 Astra: "A1 + A2 + the combined localised-ULA product theorem for `s ≥ 0`, with unlocalised A3 as a specialisation"

Agreed: A1 + A2 + A3 (localised, `s ≥ 0`, with the unlocalised specialisation).

## Result

Commit `96b2ab2` on `tide/sampler-gamma-law`; `lake build` clean, `scripts/sorries` 0/0/0/0. `Laplace/Sampler/GammaLaw.lean` (     239 lines).
A1 + A2 + A3 as voted (localised ULA for `s ≥ 0`, unlocalised as a specialisation).
`dotProduct_add_smul_mulVec`, `tiltedExpectation_exp_quadForm` (the exact partition-function ratio), `det_conj_orthoOf`,
`det_localisedPrecision`, `posDef_of_orthoOf_conj`, `laplace_localisedGibbs`, `laplace_gibbs` (`(1/√(1+s))^d` exactly),
`laplace_ulaLocalised`, `laplace_ula`.

Surprises: the sampler-side Gamma law is a ~230-line file — every ingredient (tilted Gaussians, `gaussianZ_matCLM`, the eigenbasis
lemmas of `LocalisedLLC`/`ULALocalised`) was already landed; the transform of a Gaussian quadratic form is nothing but
`Z(Q + cH)/Z(Q)`, so the Gamma(d/2, 1) law that tide 89 reaches asymptotically for the anharmonic target is exact for the Gaussian one.
