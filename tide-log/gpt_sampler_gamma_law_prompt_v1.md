You are consulted (one round) on tide 91 of an automated Lean 4 + Mathlib formalisation loop extending the `laplace` seabed
(Laplace asymptotics for Gibbs expectations, susceptibility-primer / "Sanity on Sampling" note). Zero sorry/axiom discipline.
Tides 89–90 (your consults) landed the Laplace transform of the localised anharmonic energy on E2, `→ (1+s)^{−d/2}` with its `1/t`
correction. You have repeatedly suggested a sampler-side transfer; this tide is one: the same transform for the *Gaussian* laws the
sampler files work with (the exact Gaussian Gibbs target, its localised version, and the ULA stationary law), where it is exact.

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

## Questions
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
